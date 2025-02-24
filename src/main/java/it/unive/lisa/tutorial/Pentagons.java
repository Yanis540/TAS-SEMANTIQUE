package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.*;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import it.unive.lisa.util.numeric.MathNumber;
import it.unive.lisa.util.representation.MapRepresentation;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;
import org.apache.commons.collections4.CollectionUtils;

import java.util.*;
import java.util.Map.Entry;
import java.util.function.Predicate;

/**
 * Implementation of the pentagons analysis of https://doi.org/10.1016/j.scico.2009.04.004
 */
public class Pentagons
		// instances of this class are lattice elements such that:
		// - their state (fields) hold the information contained into a whole program state
		// - they provide logic for the evaluation of expressions
		implements ValueDomain<Pentagons>,
		// we exploit BaseLattice to avoid writing common-sense logic
		BaseLattice<Pentagons> {

	// client domains are just fields of this one
	private final StrictUpperBounds upperbounds;
	private final ValueEnvironment<Interval> intervals;

	public Pentagons() {
		this(new StrictUpperBounds().top(), new ValueEnvironment<>(new Interval()).top());
	}

	public Pentagons(
			StrictUpperBounds upperbounds,
			ValueEnvironment<Interval> intervals) {
		this.upperbounds = upperbounds;
		this.intervals = intervals;
	}

	@Override
	public Pentagons top() {
		return new Pentagons(upperbounds.top(), intervals.top());
	}

	@Override
	public boolean isTop() {
		// since top() does not return a constant value, we have to override this method as well
		// providing the logic for identifying the top element
		return upperbounds.isTop() && intervals.isTop();
	}

	@Override
	public Pentagons bottom() {	return new Pentagons(upperbounds.bottom(), intervals.bottom());	}

	@Override
	public boolean isBottom() {
		// since bottom() does not return a constant value, we have to override this method as well
		// providing the logic for identifying the bottom element
		return upperbounds.isBottom() && intervals.isBottom();
	}

	@Override
	public boolean lessOrEqualAux(Pentagons other) throws SemanticException {
		if (!this.intervals.lessOrEqual(other.intervals))
			return false;

		for (Entry<Identifier, StrictUpperBounds.IdSet> entry : other.upperbounds)
			for (Identifier bound : entry.getValue()) {
				if (this.upperbounds.getState(entry.getKey()).contains(bound))
					continue;

				Interval state = this.intervals.getState(entry.getKey());
				Interval boundState = this.intervals.getState(bound);
				if (state.isBottom()
						|| boundState.isTop()
						|| state.interval.getHigh().compareTo(boundState.interval.getLow()) < 0)
					continue;

				return false;
			}

		return true;
	}

	@Override
	public Pentagons lubAux(
			Pentagons other)
			throws SemanticException {
		ValueEnvironment<Interval> newIntervals = this.intervals.lub(other.intervals);

		// lub performs the intersection between the two
		// this effectively builds s'
		StrictUpperBounds newBounds = upperbounds.lub(other.upperbounds);

		// the following builds s''
		for (Identifier x : upperbounds.getKeys()) {
			StrictUpperBounds.IdSet closure = newBounds.getState(x);

			Interval b2_x = other.intervals.getState(x);
			if (!b2_x.isBottom()) {
				for (Identifier y : upperbounds.getState(x)) {
					Interval b2_y = other.intervals.getState(y);
					if (!b2_y.isBottom() && b2_x.interval.getHigh().compareTo(b2_y.interval.getLow()) < 0) {
						closure = closure.add(y);
					}
				}
			}

			newBounds = newBounds.putState(x, closure);
		}

		// the following builds s'''
		for (Identifier x : other.upperbounds.getKeys()) {
			StrictUpperBounds.IdSet closure = newBounds.getState(x);

			Interval b1_x = intervals.getState(x);
			if (!b1_x.isBottom())
				for (Identifier y : other.upperbounds.getState(x)) {
					Interval b1_y = intervals.getState(y);
					if (!b1_y.isBottom() && b1_x.interval.getHigh().compareTo(b1_y.interval.getLow()) < 0)
						closure = closure.add(y);
				}

			newBounds = newBounds.putState(x, closure);
		}

		return new Pentagons(newBounds, newIntervals);
	}

	@Override
	public Pentagons wideningAux(
			Pentagons other)
			throws SemanticException {
		return new Pentagons(
				upperbounds.wideningAux(other.upperbounds),
				intervals.widening(other.intervals));
	}

	@Override
	public Pentagons assign(
			Identifier id,
			ValueExpression expression,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		StrictUpperBounds newBounds = upperbounds.assign(id, expression, pp, oracle);
		ValueEnvironment<Interval> newIntervals = intervals.assign(id, expression, pp, oracle);

		if (expression instanceof BinaryExpression) {
			BinaryExpression be = (BinaryExpression) expression;
			BinaryOperator op = be.getOperator();

			if (op instanceof SubtractionOperator) {
				if (be.getLeft() instanceof Identifier) {
					Identifier x = (Identifier) be.getLeft();

					if (be.getRight() instanceof Identifier) {
						// r = x - y
						Identifier y = (Identifier) be.getRight();
						if (newBounds.getState(y).contains(x)) {
							newIntervals = newIntervals.putState(id, newIntervals.getState(id)
									.glb(new Interval(MathNumber.ONE, MathNumber.PLUS_INFINITY)));
						}
						Interval intv = intervals.getState(y);
						if (!intv.isBottom() && intv.interval.getLow().compareTo(MathNumber.ZERO) > 0)
							newBounds = upperbounds.putState(id, upperbounds.getState(x).add(x));
						else
							newBounds = upperbounds.putState(id, upperbounds.lattice.top());
					}
				}
			}

		}

		return new Pentagons(newBounds, newIntervals);
	}

	@Override
	public Pentagons smallStepSemantics(
			ValueExpression expression,
			ProgramPoint pp,
			SemanticOracle oracle) throws SemanticException {
		return new Pentagons(
				upperbounds.smallStepSemantics(expression, pp, oracle),
				intervals.smallStepSemantics(expression, pp, oracle));
	}

	@Override
	public Pentagons assume(
			ValueExpression expression,
			ProgramPoint src,
			ProgramPoint dest,
			SemanticOracle oracle)
			throws SemanticException {
		return new Pentagons(
				upperbounds.assume(expression, src, dest, oracle),
				intervals.assume(expression, src, dest, oracle));
	}
	
	@Override
	public Pentagons forgetIdentifier(
			Identifier id)
			throws SemanticException {
		return new Pentagons(
				upperbounds.forgetIdentifier(id),
				intervals.forgetIdentifier(id));
	}

	@Override
	public Pentagons forgetIdentifiersIf(
			Predicate<Identifier> test)
			throws SemanticException {
		return new Pentagons(
				upperbounds.forgetIdentifiersIf(test),
				intervals.forgetIdentifiersIf(test));
	}

	@Override
	public Satisfiability satisfies(
			ValueExpression expression,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		return intervals.satisfies(expression, pp, oracle).glb(upperbounds.satisfies(expression, pp, oracle));
	}

	@Override
	public Pentagons pushScope(
			ScopeToken token)
			throws SemanticException {
		return new Pentagons(upperbounds.pushScope(token), intervals.pushScope(token));
	}

	@Override
	public Pentagons popScope(
			ScopeToken token)
			throws SemanticException {
		return new Pentagons(upperbounds.popScope(token), intervals.popScope(token));
	}

	@Override
	public StructuredRepresentation representation() {
		if (isTop())
			return Lattice.topRepresentation();
		if (isBottom())
			return Lattice.bottomRepresentation();
		Map<StructuredRepresentation, StructuredRepresentation> mapping = new HashMap<>();
		for (Identifier id : CollectionUtils.union(intervals.getKeys(), upperbounds.getKeys()))
			mapping.put(new StringRepresentation(id),
					new StringRepresentation(intervals.getState(id).toString() + ", " +
							upperbounds.getState(id).representation()));
		return new MapRepresentation(mapping);
	}

	@Override
	public int hashCode() {
		return Objects.hash(intervals, upperbounds);
	}

	@Override
	public boolean equals(
			Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Pentagons other = (Pentagons) obj;
		return Objects.equals(intervals, other.intervals) && Objects.equals(upperbounds, other.upperbounds);
	}

	@Override
	public String toString() {
		return representation().toString();
	}

	@Override
	public boolean knowsIdentifier(
			Identifier id) {
		return intervals.knowsIdentifier(id) || upperbounds.knowsIdentifier(id);
	}
}