package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.DivisionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.*;
import it.unive.lisa.symbolic.value.operator.unary.NumericNegation;
import it.unive.lisa.symbolic.value.operator.unary.StringLength;
import it.unive.lisa.symbolic.value.operator.unary.UnaryOperator;
import it.unive.lisa.util.numeric.IntInterval;
import it.unive.lisa.util.numeric.MathNumber;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.Objects;

/**
 * Basic interval operations can be found at https://en.wikipedia.org/wiki/Interval_arithmetic#Interval_operators
 *
 * Lattice operators can be found in https://doi.org/10.1016/j.scico.2009.04.004
 */
public class Interval
		// instances of this class are lattice elements such that:
		// - their state (fields) hold the information contained into a single
		//   variable
		// - they provide logic for the evaluation of expressions
		implements BaseNonRelationalValueDomain<
			// java requires this type parameter to have this class
			// as type in fields/methods
			Interval> {

	public static final Interval ZERO = new Interval(IntInterval.ZERO);
	public static final Interval TOP = new Interval(IntInterval.INFINITY);
	public static final Interval BOTTOM = new Interval(MathNumber.NaN, MathNumber.NaN);

	// the abstract information carried by this instance is an interval for a single variable
	public final IntInterval interval;

	public Interval(
			IntInterval interval) {
		this.interval = interval;
	}

	public Interval(
			MathNumber low,
			MathNumber high) {
		this(new IntInterval(low, high));
	}

	public Interval() {
		this(IntInterval.INFINITY);
	}

	@Override
	public int hashCode() {
		return Objects.hashCode(interval);
	}

	@Override
	public boolean equals(Object o) {
		if (this == o)
			return true;
		if (o == null || getClass() != o.getClass())
			return false;
		Interval interval1 = (Interval) o;
		return Objects.equals(interval, interval1.interval);
	}

	@Override
	public Interval top() {
		// the top element of the lattice
		// if this method does not return a constant value,
		// you must override the isTop() method!
		return TOP;
	}

	@Override
	public Interval bottom() {
		// the bottom element of the lattice
		// if this method does not return a constant value,
		// you must override the isBottom() method!
		return BOTTOM;
	}

	@Override
	public boolean lessOrEqualAux(
			Interval other)
			throws SemanticException {
		return other.interval.includes(interval);
	}

	@Override
	public Interval lubAux(
			Interval other)
			throws SemanticException {
		MathNumber newLow = interval.getLow().min(other.interval.getLow());
		MathNumber newHigh = interval.getHigh().max(other.interval.getHigh());
		return newLow.isMinusInfinity() && newHigh.isPlusInfinity() ? top() : new Interval(newLow, newHigh);
	}

	@Override
	public Interval glbAux(
			Interval other) {
		MathNumber newLow = interval.getLow().max(other.interval.getLow());
		MathNumber newHigh = interval.getHigh().min(other.interval.getHigh());

		if (newLow.compareTo(newHigh) > 0)
			return bottom();
		return newLow.isMinusInfinity() && newHigh.isPlusInfinity() ? top() : new Interval(newLow, newHigh);
	}

	@Override
	public Interval wideningAux(
			Interval other)
			throws SemanticException {
		MathNumber newLow, newHigh;
		if (other.interval.getHigh().compareTo(interval.getHigh()) > 0)
			newHigh = MathNumber.PLUS_INFINITY;
		else
			newHigh = interval.getHigh();

		if (other.interval.getLow().compareTo(interval.getLow()) < 0)
			newLow = MathNumber.MINUS_INFINITY;
		else
			newLow = interval.getLow();

		return newLow.isMinusInfinity() && newHigh.isPlusInfinity() ? top() : new Interval(newLow, newHigh);
	}

	@Override
	public StructuredRepresentation representation() {
		// this method serializes instances of this domain
		// to a json-compatible format that will be used for dumping
		if (isBottom())
			return Lattice.bottomRepresentation();

		return new StringRepresentation(interval.toString());
	}

	@Override
	public String toString() {
		return representation().toString();
	}

	// logic for evaluating expressions below

	@Override
	public Interval evalNonNullConstant(
			Constant constant,
			ProgramPoint pp,
			SemanticOracle oracle) {
		if (constant.getValue() instanceof Integer) {
			Integer i = (Integer) constant.getValue();
			return new Interval(new MathNumber(i), new MathNumber(i));
		}

		return top();
	}

	@Override
	public Interval evalUnaryExpression(
			UnaryOperator operator,
			Interval arg,
			ProgramPoint pp,
			SemanticOracle oracle) {
		if (operator == NumericNegation.INSTANCE)
			if (arg.isTop())
				return top();
			else
				return new Interval(arg.interval.mul(IntInterval.MINUS_ONE));
		else if (operator == StringLength.INSTANCE)
			return new Interval(MathNumber.ZERO, MathNumber.PLUS_INFINITY);
		else
			return top();
	}

	@Override
	public Interval evalBinaryExpression(
			BinaryOperator operator,
			Interval left,
			Interval right,
			ProgramPoint pp,
			SemanticOracle oracle) {
		if (!(operator instanceof DivisionOperator) && (left.isTop() || right.isTop()))
			// with div, we can return zero or bottom even if one of the
			// operands is top
			return top();

		if (operator instanceof AdditionOperator)
			return new Interval(left.interval.plus(right.interval));
		else if (operator instanceof SubtractionOperator)
			return new Interval(left.interval.diff(right.interval));
		else if (operator instanceof MultiplicationOperator)
			if (left.equals(ZERO) || right.equals(ZERO))
				return ZERO;
			else
				return new Interval(left.interval.mul(right.interval));
		else if (operator instanceof DivisionOperator)
			if (right.equals(ZERO))
				return bottom();
			else if (left.equals(ZERO))
				return ZERO;
			else if (left.isTop() || right.isTop())
				return top();
			else {
				Interval div = new Interval(left.interval.div(right.interval, false, false));
				if (div.equals(BOTTOM))
					return bottom();
				return div;
			}
		return top();
	}

	@Override
	public Satisfiability satisfiesBinaryExpression(
			BinaryOperator operator,
			Interval left,
			Interval right,
			ProgramPoint pp,
			SemanticOracle oracle) {
		if (left.isTop() || right.isTop())
			return Satisfiability.UNKNOWN;

		if (operator == ComparisonEq.INSTANCE) {
			Interval glb = null;
			try {
				glb = left.glb(right);
			} catch (SemanticException e) {
				return Satisfiability.UNKNOWN;
			}

			if (glb.isBottom())
				return Satisfiability.NOT_SATISFIED;
			else if (left.interval.isSingleton() && left.equals(right))
				return Satisfiability.SATISFIED;
			return Satisfiability.UNKNOWN;
		} else if (operator == ComparisonGe.INSTANCE)
			return satisfiesBinaryExpression(ComparisonLe.INSTANCE, right, left, pp, oracle);
		else if (operator == ComparisonGt.INSTANCE)
			return satisfiesBinaryExpression(ComparisonLt.INSTANCE, right, left, pp, oracle);
		else if (operator == ComparisonLe.INSTANCE) {
			Interval glb = null;
			try {
				glb = left.glb(right);
			} catch (SemanticException e) {
				return Satisfiability.UNKNOWN;
			}

			if (glb.isBottom())
				return Satisfiability.fromBoolean(left.interval.getHigh().compareTo(right.interval.getLow()) <= 0);
			// we might have a singleton as glb if the two intervals share a
			// bound
			if (glb.interval.isSingleton() && left.interval.getHigh().compareTo(right.interval.getLow()) == 0)
				return Satisfiability.SATISFIED;
			return Satisfiability.UNKNOWN;
		} else if (operator == ComparisonLt.INSTANCE) {
			Interval glb = null;
			try {
				glb = left.glb(right);
			} catch (SemanticException e) {
				return Satisfiability.UNKNOWN;
			}

			if (glb.isBottom())
				return Satisfiability.fromBoolean(left.interval.getHigh().compareTo(right.interval.getLow()) < 0);
			return Satisfiability.UNKNOWN;
		} else if (operator == ComparisonNe.INSTANCE) {
			Interval glb = null;
			try {
				glb = left.glb(right);
			} catch (SemanticException e) {
				return Satisfiability.UNKNOWN;
			}
			if (glb.isBottom())
				return Satisfiability.SATISFIED;
			return Satisfiability.UNKNOWN;
		}
		return Satisfiability.UNKNOWN;
	}

	@Override
	public ValueEnvironment<Interval> assumeBinaryExpression(
			ValueEnvironment<Interval> environment,
			BinaryOperator operator,
			ValueExpression left,
			ValueExpression right,
			ProgramPoint src,
			ProgramPoint dest,
			SemanticOracle oracle)
			throws SemanticException {
		Identifier id;
		Interval eval;
		boolean rightIsExpr;
		if (left instanceof Identifier) {
			eval = eval(right, environment, src, oracle);
			id = (Identifier) left;
			rightIsExpr = true;
		} else if (right instanceof Identifier) {
			eval = eval(left, environment, src, oracle);
			id = (Identifier) right;
			rightIsExpr = false;
		} else
			return environment;

		Interval starting = environment.getState(id);
		if (eval.isBottom() || starting.isBottom())
			return environment.bottom();

		boolean lowIsMinusInfinity = eval.interval.lowIsMinusInfinity();
		Interval low_inf = new Interval(eval.interval.getLow(), MathNumber.PLUS_INFINITY);
		Interval lowp1_inf = new Interval(eval.interval.getLow().add(MathNumber.ONE), MathNumber.PLUS_INFINITY);
		Interval inf_high = new Interval(MathNumber.MINUS_INFINITY, eval.interval.getHigh());
		Interval inf_highm1 = new Interval(MathNumber.MINUS_INFINITY, eval.interval.getHigh().subtract(MathNumber.ONE));

		Interval update = null;
		if (operator == ComparisonEq.INSTANCE)
			update = eval;
		else if (operator == ComparisonGe.INSTANCE)
			if (rightIsExpr)
				update = lowIsMinusInfinity ? null : starting.glb(low_inf);
			else
				update = starting.glb(inf_high);
		else if (operator == ComparisonGt.INSTANCE)
			if (rightIsExpr)
				update = lowIsMinusInfinity ? null : starting.glb(lowp1_inf);
			else
				update = lowIsMinusInfinity ? eval : starting.glb(inf_highm1);
		else if (operator == ComparisonLe.INSTANCE)
			if (rightIsExpr)
				update = starting.glb(inf_high);
			else
				update = lowIsMinusInfinity ? null : starting.glb(low_inf);
		else if (operator == ComparisonLt.INSTANCE)
			if (rightIsExpr)
				update = lowIsMinusInfinity ? eval : starting.glb(inf_highm1);
			else
				update = lowIsMinusInfinity ? null : starting.glb(lowp1_inf);

		if (update == null)
			return environment;
		else if (update.isBottom())
			return environment.bottom();
		else
			return environment.putState(id, update);
	}
}