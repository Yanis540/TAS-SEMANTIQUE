package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.program.annotations.Annotation;
import it.unive.lisa.program.annotations.Annotations;
import it.unive.lisa.program.annotations.matcher.AnnotationMatcher;
import it.unive.lisa.program.annotations.matcher.BasicAnnotationMatcher;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.*;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import it.unive.lisa.symbolic.value.operator.ternary.TernaryOperator;
import it.unive.lisa.symbolic.value.operator.unary.UnaryOperator;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.Objects;

public class Taint
		// instances of this class are lattice elements such that:
		// - their state (fields) hold the information contained into a single
		//   variable
		// - they provide logic for the evaluation of expressions
		implements
		BaseNonRelationalValueDomain<
				// java requires this type parameter to have this class
				// as type in fields/methods
				Taint> {

	/**
	 * The annotation used to mark tainted variables.
	 */
	public static final Annotation TAINTED_ANNOTATION = new Annotation("lisa.taint.Tainted");

	/**
	 * The annotation used to mark clean variables, that is, sanitizers of tainted information.
	 */
	public static final Annotation CLEAN_ANNOTATION = new Annotation("lisa.taint.Clean");

	/**
	 * An {@link AnnotationMatcher} for {@link #TAINTED_ANNOTATION}. Annotation matchers are just utility objects that
	 * 	 * allow for conditional matching of annotations based on names, parameters, ...
	 */
	public static final AnnotationMatcher TAINTED_MATCHER = new BasicAnnotationMatcher(TAINTED_ANNOTATION);

	/**
	 * An {@link AnnotationMatcher} for {@link #CLEAN_ANNOTATION}. Annotation matchers are just utility objects that
	 * allow for conditional matching of annotations based on names, parameters, ...
	 */
	public static final AnnotationMatcher CLEAN_MATCHER = new BasicAnnotationMatcher(CLEAN_ANNOTATION);

	// as this is a finite lattice, we can optimize by having constant elements
	// for each of them
	private static final Taint TAINT = new Taint(true);
	private static final Taint CLEAN = new Taint(false);
	private static final Taint BOTTOM = new Taint(null);

	// this is just to distinguish the three elements
	private final Boolean taint;

	public Taint() {
		this(true);
	}

	public Taint(
			Boolean taint) {
		this.taint = taint;
	}

	public boolean isPossiblyTainted() {
		return this == TAINT;
	}

	@Override
	public boolean equals(
			Object o) {
		if (this == o)
			return true;
		if (o == null || getClass() != o.getClass())
			return false;
		Taint taint1 = (Taint) o;
		return Objects.equals(taint, taint1.taint);
	}

	@Override
	public int hashCode() { return Objects.hashCode(taint);	}

	@Override
	public Taint top() {
		// the top element of the lattice
		// if this method does not return a constant value,
		// you must override the isTop() method!
		return TAINT;
	}

	@Override
	public Taint bottom() {
		// the bottom element of the lattice
		// if this method does not return a constant value,
		// you must override the isBottom() method!
		return BOTTOM;
	}

	@Override
	public boolean lessOrEqualAux(
			Taint other)
			throws SemanticException {
		// since this lattice is on a straight line, we never end up here
		return false;
	}

	@Override
	public Taint lubAux(
			Taint other)
			throws SemanticException {
		// since this lattice is on a straight line, we never end up here
		return TAINT;
	}

	@Override
	public StructuredRepresentation representation() {
		// this method serializes instances of this domain
		// to a json-compatible format that will be used for dumping
		if (this == BOTTOM)
			return Lattice.bottomRepresentation();
		if (this == CLEAN)
			return new StringRepresentation("_");
		return new StringRepresentation("#");
	}

	// logic for evaluating expressions below

	@Override
	public Taint evalIdentifier(
			Identifier id,
			ValueEnvironment<Taint> environment,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		// we rely on annotations to force the evaluation of
		// variables to their taintedness values
		// this works because LiSA stores the returned value of
		// function calls in temporary variables
		Annotations annots = id.getAnnotations();
		if (annots.isEmpty())
			return BaseNonRelationalValueDomain.super.evalIdentifier(id, environment, pp, oracle);

		if (annots.contains(TAINTED_MATCHER))
			return TAINT;

		if (annots.contains(CLEAN_MATCHER))
			return CLEAN;

		return BaseNonRelationalValueDomain.super.evalIdentifier(id, environment, pp, oracle);
	}

	@Override
	public Taint evalNullConstant(
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		return CLEAN;
	}

	@Override
	public Taint evalNonNullConstant(
			Constant constant,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		return CLEAN;
	}

	@Override
	public Taint evalUnaryExpression(
			UnaryOperator operator,
			Taint arg,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		return arg;
	}

	@Override
	public Taint evalBinaryExpression(
			BinaryOperator operator,
			Taint left,
			Taint right,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		return left.lub(right);
	}

	@Override
	public Taint evalTernaryExpression(
			TernaryOperator operator,
			Taint left,
			Taint middle,
			Taint right,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		return left.lub(middle).lub(right);
	}

	@Override
	public Taint evalTypeCast(
			BinaryExpression cast,
			Taint left,
			Taint right,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		return left;
	}

	@Override
	public Taint evalTypeConv(
			BinaryExpression conv,
			Taint left,
			Taint right,
			ProgramPoint pp,
			SemanticOracle oracle)
			throws SemanticException {
		return left;
	}
}