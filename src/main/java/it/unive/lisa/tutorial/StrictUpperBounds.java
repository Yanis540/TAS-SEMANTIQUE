package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.InverseSetLattice;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.Environment;
import it.unive.lisa.analysis.nonrelational.NonRelationalDomain;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.*;

import java.util.*;

/**
 * Relational implementation of the upper bounds analysis of https://doi.org/10.1016/j.scico.2009.04.004
 */
public class StrictUpperBounds
		// instances of this class are lattice elements such that:
		// - their state (fields) hold the information for all variables
		// - they provide logic for the evaluation of statements, traversing conditions, ...
		extends
		// we reuse the value environment to simplify our implementation, but to do this we
		// have to make IdSet an NRVD even if we do not need it
		Environment<StrictUpperBounds, ValueExpression, StrictUpperBounds.IdSet>
		// we make explicit that this is a value domain
		implements ValueDomain<StrictUpperBounds> {

	public StrictUpperBounds() {
		super(new IdSet(Collections.emptySet()).top());
	}

	public StrictUpperBounds(
			IdSet lattice,
			Map<Identifier, IdSet> function) {
		super(lattice, function);
	}

	@Override
	public StrictUpperBounds mk(
			IdSet lattice,
			Map<Identifier, IdSet> function) {
		return new StrictUpperBounds(lattice, function);
	}

	@Override
	public StrictUpperBounds top() {
		return new StrictUpperBounds(lattice.top(), null);
	}

	@Override
	public StrictUpperBounds bottom() {
		return new StrictUpperBounds(lattice.bottom(), null);
	}

	@Override
	public StrictUpperBounds assign(
			Identifier id,
			ValueExpression expression,
			ProgramPoint pp,
			SemanticOracle oracle) throws SemanticException {
		// cleanup: if a variable is reassigned, it can no longer be an upperbound of other variables
		Map<Identifier, IdSet> cleanup = new HashMap<>();
		for (Map.Entry<Identifier, IdSet> entry : this) {
			if (entry.getKey().equals(id))
				continue;
			if (!entry.getValue().contains(id))
				cleanup.put(entry.getKey(), entry.getValue());

			Set<Identifier> copy = new HashSet<>(entry.getValue().elements);
			copy.remove(id);
			cleanup.put(entry.getKey(), new IdSet(copy));
		}

		if (expression instanceof BinaryExpression) {
			BinaryExpression be = (BinaryExpression) expression;
			BinaryOperator op = be.getOperator();

			if (op instanceof SubtractionOperator
					&& be.getLeft() instanceof Identifier
					&& be.getRight() instanceof Constant
					&& !be.getLeft().equals(id)) {
				// id = y - c (where 2 is the constant)
				Identifier y = (Identifier) be.getLeft();
				cleanup.put(id, getState(y).add(y));
			}
		}

		return new StrictUpperBounds(lattice, cleanup);
	}

	@Override
	public StrictUpperBounds smallStepSemantics(
			ValueExpression expression,
			ProgramPoint pp,
			SemanticOracle oracle) throws SemanticException {
		// nothing to do
		return this;
	}

	@Override
	public Satisfiability satisfies(
			ValueExpression expression,
			ProgramPoint pp,
			SemanticOracle oracle) throws SemanticException {
		if (!(expression instanceof BinaryExpression))
			return Satisfiability.UNKNOWN;

		BinaryExpression bexp = (BinaryExpression) expression;
		SymbolicExpression left = bexp.getLeft();
		SymbolicExpression right = bexp.getRight();
		BinaryOperator operator = bexp.getOperator();

		if (!(left instanceof Identifier && right instanceof Identifier))
			// we only process conditions between variables
			return Satisfiability.UNKNOWN;

		Identifier x = (Identifier) left;
		Identifier y = (Identifier) right;

		if (operator instanceof ComparisonLt) {
			return Satisfiability.fromBoolean(getState(x).contains(y));
		} else if (operator instanceof ComparisonLe) {
			if (getState(x).contains(y))
				return Satisfiability.SATISFIED;
			return Satisfiability.UNKNOWN;
		} else if (operator instanceof ComparisonGt) {
			return Satisfiability.fromBoolean(getState(y).contains(x));
		} else if (operator instanceof ComparisonGe) {
			if (getState(y).contains(x))
				return Satisfiability.SATISFIED;
			return Satisfiability.UNKNOWN;
		}

		return Satisfiability.UNKNOWN;
	}

	@Override
	public StrictUpperBounds assume(
			ValueExpression expression,
			ProgramPoint src,
			ProgramPoint dest,
			SemanticOracle oracle) throws SemanticException {
		if (!(expression instanceof BinaryExpression))
			return this;

		BinaryExpression bexp = (BinaryExpression) expression;
		SymbolicExpression left = bexp.getLeft();
		SymbolicExpression right = bexp.getRight();
		BinaryOperator operator = bexp.getOperator();

		if (!(left instanceof Identifier && right instanceof Identifier))
			// we only process conditions between variables
			return this;

		Identifier x = (Identifier) left;
		Identifier y = (Identifier) right;

		if (operator instanceof ComparisonLt) {
			// [[x < y]](s) = s[x -> s(x) U s(y) U {y}]
			IdSet s_x = getState(x);
			IdSet s_y = getState(y);
			IdSet y_singleton = new IdSet(Collections.singleton(y));
			IdSet set = s_x.glb(s_y).glb(y_singleton);
			return putState(x, set);
		} else if (operator instanceof ComparisonEq) {
			// [[x == y]](s) = s[x,y -> s(x) U s(y)]
			IdSet s_x = getState(x);
			IdSet s_y = getState(y);
			IdSet set = s_x.glb(s_y);
			return putState(x, set).putState(y, set);
		} else if (operator instanceof ComparisonLe) {
			// [[x <= y]](s) = s[x -> s(x) U s(y)]
			IdSet s_x = getState(x);
			IdSet s_y = getState(y);
			IdSet set = s_x.glb(s_y);
			return putState(x, set);
		} else if (operator instanceof ComparisonGt) {
			// x > y --> y < x
			return assume(
					new BinaryExpression(
							expression.getStaticType(),
							right,
							left,
							ComparisonLt.INSTANCE,
							expression.getCodeLocation()),
					src,
					dest,
					oracle);
		} else if (operator instanceof ComparisonGe) {
			// x >= y --> y <= x
			return assume(
					new BinaryExpression(
							expression.getStaticType(),
							right,
							left,
							ComparisonLe.INSTANCE,
							expression.getCodeLocation()),
					src,
					dest,
					oracle);
		}

		return this;
	}

	public static class IdSet
			// instances of this class are lattice elements such that:
			// - their state (fields) hold the information contained into a single
			//   variable
			extends
			// the inverse set lattice is a lattice implementation provided by LiSA that uses:
			// - sets of elements as the abstract information carried by each lattice instance
			// - superset inclusion as partial order
			// - set intersection as lub
			// - set union as glb
			// this makes it so the less information you have, the more you are close to the top element
			InverseSetLattice<IdSet, Identifier>
			// this is a hack: we do not need the NRVD structure here, but we use it to
			// plug this class inside environments
			implements NonRelationalDomain<IdSet, ValueExpression, StrictUpperBounds> {

		/**
		 * Builds the lattice.
		 *
		 * @param elements the elements that are contained in the lattice
		 */
		public IdSet(
				Set<Identifier> elements) {
			super(elements, elements.isEmpty());
		}

		/**
		 * Builds the lattice.
		 *
		 * @param elements the elements that are contained in the lattice
		 * @param isTop    whether or not this is the top or bottom element of the lattice, valid only if the set of
		 *                 elements is empty
		 */
		public IdSet(
				Set<Identifier> elements,
				boolean isTop) {
			super(elements, isTop);
		}

		@Override
		public IdSet wideningAux(IdSet other) throws SemanticException {
			// widening as provided in the paper
			return other.elements.containsAll(elements) ? other : top();
		}

		@Override
		public IdSet top() {
			// isTop() is already redefined in the superclass
			return new IdSet(Collections.emptySet(), true);
		}

		@Override
		public IdSet bottom() {
			// isBottom() is already redefined in the superclass
			return new IdSet(Collections.emptySet(), false);
		}

		@Override
		public IdSet mk(Set<Identifier> set) {
			return new IdSet(set);
		}

		public IdSet add(
				Identifier id) {
			Set<Identifier> res = new HashSet<>(elements);
			res.add(id);
			return new IdSet(res);
		}

		@Override
		public IdSet eval(
				ValueExpression expression,
				StrictUpperBounds environment,
				ProgramPoint pp,
				SemanticOracle oracle) throws SemanticException {
			// since this won't be really used as a non relational domain,
			// we don't care about the implementation of this method
			return top();
		}

		@Override
		public Satisfiability satisfies(
				ValueExpression expression,
				StrictUpperBounds environment,
				ProgramPoint pp,
				SemanticOracle oracle) throws SemanticException {
			// since this won't be really used as a non relational domain,
			// we don't care about the implementation of this method
			return Satisfiability.UNKNOWN;
		}

		@Override
		public StrictUpperBounds assume(
				StrictUpperBounds environment,
				ValueExpression expression,
				ProgramPoint src,
				ProgramPoint dest,
				SemanticOracle oracle) throws SemanticException {
			// since this won't be really used as a non relational domain,
			// we don't care about the implementation of this method
			return environment;
		}

		@Override
		public boolean canProcess(
				SymbolicExpression expression,
				ProgramPoint pp,
				SemanticOracle oracle) {
			// since this won't be really used as a non relational domain,
			// we don't care about the implementation of this method
			return true;
		}
	}
}
