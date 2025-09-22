/******************************************************************************
 * Top contributors (to current version):
 *   anynomous author
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Optimizer for Integer type.
 */

#include "omt/omt_opt_mcsat.h"

#include "options/smt_options.h"
#include "smt/solver_engine.h"

// anynomous author: pre-check
#include "theory/smt_engine_subsolver.h"

// anynomous author: RealAlgebraicNumber
#include "util/real_algebraic_number.h"

using namespace cvc5::internal::smt;
namespace cvc5::internal::omt {

bool trapped(const Node& value, const Node& pre_value){
  // 1. the new value is too large
  // std::cout<<"opt value:"<<value.getConst<Rational>()<<std::endl;
  if(value.getConst<Rational>() >= cvc5::internal::Rational(1000000) || value.getConst<Rational>() <= cvc5::internal::Rational(-1000000)){
    // std::cout<<value.getConst<Rational>()<<" - "<<pre_value.getConst<Rational>()<<std::endl;
    return true;
  }
  // 2. the difference is too small
  else if((value.getConst<Rational>()-pre_value.getConst<Rational>()) < cvc5::internal::Rational(10)){
    // std::cout<<value.getConst<Rational>()<<" - "<<pre_value.getConst<Rational>()<<std::endl;
    return true;
  }
  return false;
}

OptimizationResult OMTOptimizerMCSAT::optimize(SolverEngine* optChecker,
                                                 TNode target,
                                                 bool isMinimize)
{
  // anynomous author: opt-mcsat search for goal
  //      the smt engine to which we send intermediate queries.
  // new functions:
  //  setObjectiveVariable: set the objective variable
  //  getBoundValue: return the bound value in the cell
  //  getOptimizedValue: return the optimized value in the cell
  //  missBound: whether the bound is checked.
  if(target.isConst()){
    std::cerr<<"Objective is a constant"<<std::endl;
    d_optPreChecker = createOptPreChecker(optChecker);
    d_optPreChecker->push();
    Result intermediateSatResult;
    intermediateSatResult = d_optPreChecker->checkSat();
    d_optPreChecker->pop();
    return OptimizationResult(intermediateSatResult, target);
  }

  Node optimized_value;
  NodeManager* nm = NodeManager::currentNM();
  bool has_symba = false;
  Node value;
  Node increment;
  Kind incrementalOperator = kind::NULL_EXPR;
  Result intermediateSatResult;
  bool isTrapped = false;
  
  if (has_symba){
    // 2023-05-30: now use symba architecture
    Node pre_value;
    d_optPreChecker = createOptPreChecker(optChecker);
    d_optPreChecker->push();
    intermediateSatResult = d_optPreChecker->checkSat();
    d_optPreChecker->pop();
    if (intermediateSatResult.isUnknown()
        || intermediateSatResult.getStatus() == Result::UNSAT)
    {
      return OptimizationResult(intermediateSatResult, value);
    }
    // node storing target > old_value (used in optimization loop)
    if (isMinimize)
    {
      // if objective is minimize,
      // then assert optimization_target < current_model_value
      incrementalOperator = kind::LT;
    }
    else
    {
      // if objective is maximize,
      // then assert optimization_target > current_model_value
      incrementalOperator = kind::GT;
    }
    // Result lastSatResult = intermediateSatResult;
    // Workhorse of linear search:
    // This loop will keep incrmenting/decrementing the objective until unsat
    // When unsat is hit,
    // the optimized value is the model value just before the unsat call
    value = d_optPreChecker->getValue(target);
    while (intermediateSatResult.getStatus() == Result::SAT)
    {
      Assert(!value.isNull());
      increment = nm->mkNode(incrementalOperator, target, value);
      d_optPreChecker->assertFormula(increment);
      intermediateSatResult = d_optPreChecker->checkSat();
      pre_value = value;
      if(intermediateSatResult.getStatus() == Result::UNSAT) break;
      value = d_optPreChecker->getValue(target);
      if(trapped(value, pre_value)){
        isTrapped = true; // anynomous author: if break -> isTrapped = true (must)
        // anynomous author: 2023-08-21: we have to check whether x < value leads to unsat.
        //      If unsat, it means that x = value is the optimal;
        //      If sat, it means that optimal hides in x < value.
        increment = nm->mkNode(incrementalOperator, target, value);
        d_optPreChecker->assertFormula(increment);
        intermediateSatResult = d_optPreChecker->checkSat();
        if(intermediateSatResult.getStatus() == Result::UNSAT){
          // Assertion: the optimal is not unbounded and not approximate value.
          return OptimizationResult(Result(Result::SAT, intermediateSatResult.getInputName()), value);
        }
        break;
      }
    }
    d_optPreChecker->pop();
    if(!isTrapped && intermediateSatResult.getStatus() == Result::UNSAT){
      // anynomous author: for example, we find x = 1 and add an incremental lemma x < 1.
      //      Then it tells unsat, which means that x = 1 is the optimal.
      //      Maybe d_optPreChecker's first check directly find the optimal.
      //      condition: not trapped && UNSAT
      //      Assertion: the optimal is not unbounded and not approximate value.
      return OptimizationResult(Result(Result::SAT, intermediateSatResult.getInputName()), value);
    }
  } // end of symba

  // opt_cdcac
  // anynomous author: _opt_var stores the target as a variable
  Node _opt_var;
  // std::cout<<"before invoking opt..."<<std::endl;
  // for(size_t i=0;i<optChecker->getAssertions().size();i++){
  //   std::cout<<optChecker->getAssertions()[i]<<std::endl;
  // }
  // set optChecker as optimizer
  optChecker->setOptimization();
  if(target.isVar()){
    _opt_var = target;
    optChecker->setObjective(isMinimize, _opt_var);
    if(has_symba && isTrapped){
      increment = nm->mkNode(incrementalOperator, _opt_var, value);
      optChecker->assertFormula(increment); // anynomous author: 2023-08-16: add pre-lemma
    }
  }
  else{
    // _opt_var = nm->mkBoundVar(nm->realType());
    // get type from target from NRA/NIA/NIRA
    _opt_var = nm->mkBoundVar(target.getType());
    // Node objectiveEquation = nm->mkNode(kind::EQUAL,_opt_var,target);
    // optChecker->assertFormula(objectiveEquation);
    optChecker->setObjective(isMinimize, _opt_var);
    optChecker->assertFormula(nm->mkNode(kind::EQUAL,_opt_var,target));
    if(has_symba && isTrapped){
      increment = nm->mkNode(incrementalOperator, _opt_var, value);
      optChecker->assertFormula(increment); // anynomous author: 2023-08-16: add pre-lemma
    }
  }
  // anynomous author: TODO, vlaue 有时候会取整，注意看一下会不会出错
  // std::cout<<value<<std::endl;
  
  // std::cout<<"before invoking opt 2..."<<std::endl;
  // for(size_t i=0;i<optChecker->getAssertions().size();i++){
  //   std::cout<<optChecker->getAssertions()[i]<<std::endl;
  // }
  // if(isMinimize) optChecker->assertFormula(nm->mkNode(kind::LEQ,_opt_var,value));
  // else optChecker->assertFormula(nm->mkNode(kind::GEQ,_opt_var,value));
  // anynomous author: set the variable to optimize
  optChecker->push();
  // for(size_t i=0;i<optChecker->getAssertions().size();i++){
  //   std::cout<<optChecker->getAssertions()[i]<<std::endl;
  // }

  intermediateSatResult = optChecker->checkSat();
  if(optChecker->isOptSAT()){
    intermediateSatResult = Result(
      Result::SAT,
      intermediateSatResult.getInputName()
    );
  }
  else if (intermediateSatResult.isUnknown() || intermediateSatResult.getStatus() == Result::UNSAT)
  {
    return OptimizationResult(intermediateSatResult, optimized_value);
  }
  // sat
  Result lastSatResult = intermediateSatResult;
  if(!optChecker->isOptUnbounded()){
    // optChecker->buildOptModel();
    optimized_value = optChecker->getOptimizedValue(_opt_var);
  }

  optChecker->pop(); // TODO, how to use push / pop? 
  // optChecker->unsetObjective(); // anynomous author: once optimize, do not invoke setObjective? 
  if(!optChecker->isOptUnbounded()){
    return OptimizationResult(lastSatResult, optimized_value);
  }
  else{
    if(optChecker->isOptPosInf()) 
      return OptimizationResult(lastSatResult, optimized_value, OptimizationResult::POSTITIVE_INF);
    else if(optChecker->isOptNegInf())
      return OptimizationResult(lastSatResult, optimized_value, OptimizationResult::NEGATIVE_INF);
    else{ // isApprox
      optimized_value = optChecker->getOptimizedValue(_opt_var);
      if(optChecker->isOptPosApprox()) // a + \epsilon
        return OptimizationResult(lastSatResult, optimized_value, OptimizationResult::POSTITIVE_EPSILON);
      else // (optChecker->isOptNegApprox())
        return OptimizationResult(lastSatResult, optimized_value, OptimizationResult::NEGATIVE_EPSILON);
    }
  }
}

OptimizationResult OMTOptimizerMCSAT::minimize(SolverEngine* optChecker,
                                                 TNode target)
{
  return this->optimize(optChecker, target, true);
}
OptimizationResult OMTOptimizerMCSAT::maximize(SolverEngine* optChecker,
                                                 TNode target)
{
  return this->optimize(optChecker, target, false);
}

std::unique_ptr<SolverEngine> OMTOptimizerMCSAT::createOptPreChecker(SolverEngine* parentSMTSolver){
  // anynomous author: it will not use the original SolverEngine
  std::unique_ptr<SolverEngine> preOptChecker;
  // initializeSubSolver will copy the options and theories enabled
  // from the current solver to optChecker and adds timeout
  theory::initializeSubsolver(
      preOptChecker, parentSMTSolver->getEnv(), false, 0);
  // we need to be in incremental mode for multiple objectives since we need to
  // push pop we need to produce models to inrement on our objective
  preOptChecker->setOption("incremental", "true");
  preOptChecker->setOption("produce-models", "true");
  // Move assertions from the parent solver to the subsolver
  std::vector<Node> p_assertions = parentSMTSolver->getSubstitutedAssertions();
  for (const Node& e : p_assertions)
  {
    preOptChecker->assertFormula(e);
  }
  return preOptChecker;
}


// void OMTOptimizerMCSAT::phase_reconstruct(){
//   // SolverEngine* d_optPreChecker, SolverEngine* optChecker

// }

}  // namespace cvc5::internal::omt
