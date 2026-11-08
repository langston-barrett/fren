module

import all scratch.expr.Prototype

#print axioms ExprPrototype.fold
#print axioms ExprPrototype.Layer.mapChildrenM
#print axioms ExprPrototype.rename
#print axioms ExprPrototype.shift
#print axioms ExprPrototype.subst
#print axioms ExprPrototype.rename_scoped
#print axioms ExprPrototype.subst_scoped
#print axioms ExprPrototype.substTop_closed_scoped
#print axioms ExprPrototype.scopeCheck_iff

-- Print the accepted equations and termination implementation, not just a claim
-- that the compiler admitted these declarations.
#print ExprPrototype.fold.eq_5
#print ExprPrototype.fold
#print ExprPrototype.substTop_closed_scoped
