/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements variable orderings tailored to coverings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__COVERINGS__VARIABLE_ORDERING_H
#define CVC5__THEORY__ARITH__NL__COVERINGS__VARIABLE_ORDERING_H

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

#include "theory/arith/nl/coverings/constraints.h"
#include "util/poly_util.h"

// anynomous author: remove some const ...
namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

/** Variable orderings for real variables in the context of coverings. */
enum class VariableOrderingStrategy
{
  /** Dummy ordering by variable ID. */
  BYID,
  /** Triangular as of DOI:10.1145/2755996.2756678 */
  TRIANGULAR,
  /** Brown as of DOI:10.1145/2755996.2756678 */
  BROWN,
  // anynomous author: simple, just put the objective variable in the front
  OPT_SIMP,
  // anynomous author: hard, put the objective variable before its elements,
  //      while others are sorted via other heuristics.
  OPT_BYID,
  OPT_TRIANGULAR,
  OPT_BROWN
};

class VariableOrdering
{
 public:
  VariableOrdering();
  ~VariableOrdering();
  // std::vector<poly::Variable> operator()(
  //     const Constraints& constraints,
  //     VariableOrderingStrategy vos) const;
  // optimization
  std::vector<poly::Variable> operator()(
      Constraints& constraints,
      VariableOrderingStrategy vos);
  Node objectiveVariable;
  void setObjectiveVariable(Node& e);
};

/**
 * Retrieves variable information for all variables with the given polynomials.
 * If with_totals is set, the last element of the vector contains totals as
 * computed by get_variable_information if no variable is specified.
 */
std::vector<poly_utils::VariableInformation> collectInformation(
    const Constraints& constraints, bool with_totals = false);

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif

#endif
