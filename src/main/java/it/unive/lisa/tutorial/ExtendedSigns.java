package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.program.cfg.statement.Assignment;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.Variable;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.DivisionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.*;
import it.unive.lisa.symbolic.value.operator.unary.NumericNegation;
import it.unive.lisa.symbolic.value.operator.unary.UnaryOperator;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.HashSet;
import java.util.Objects;

public class ExtendedSigns implements BaseNonRelationalValueDomain<ExtendedSigns> {

    private static final ExtendedSigns BOTTOM = new ExtendedSigns(Integer.MIN_VALUE);
    private static final ExtendedSigns NEGATIVE = new ExtendedSigns(-2);
    private static final ExtendedSigns STRICTLY_NEGATIVE = new ExtendedSigns(-1);
    private static final ExtendedSigns ZERO = new ExtendedSigns(0);
    private static final ExtendedSigns STRICTLY_POSITIVE = new ExtendedSigns(1);
    private static final ExtendedSigns NON_ZERO = new ExtendedSigns(2);
    private static final ExtendedSigns POSITIVE = new ExtendedSigns(3);
    private static final ExtendedSigns TOP = new ExtendedSigns(Integer.MAX_VALUE);
    public int sign;
    public int value; 
    public ExtendedSigns() {
        this.sign = Integer.MAX_VALUE;
    }
    public ExtendedSigns(int sign) {
        this.sign = sign;
    }

    @Override
    public ExtendedSigns top() {
        return TOP;
    }

    @Override
    public ExtendedSigns bottom() {
        return BOTTOM;
    }

    @Override
    public boolean lessOrEqualAux(ExtendedSigns other) {
        // return this.equals(other) || other == TOP;
        return false;
    }

    @Override
    public ExtendedSigns lubAux(ExtendedSigns other) {
        // if (this.equals(other)) return this;
        if(this == TOP || other == TOP) return TOP;
        if(this == BOTTOM || other == BOTTOM) return BOTTOM;
        if(this == ZERO) {
            if(other == ZERO) return ZERO;
            if(other == STRICTLY_POSITIVE) return POSITIVE;
            if(other == STRICTLY_NEGATIVE) return NEGATIVE;
            return other;
        }
        if(other == ZERO) {
            if(this == ZERO) return ZERO;
            if(this == STRICTLY_POSITIVE) return POSITIVE;
            if(this == STRICTLY_NEGATIVE) return NEGATIVE;
            return this;
        }
        if(this == NEGATIVE && other == STRICTLY_NEGATIVE || this == STRICTLY_NEGATIVE && other == NEGATIVE) return NEGATIVE;
        if(this == POSITIVE && other == STRICTLY_POSITIVE || this == STRICTLY_POSITIVE && other == POSITIVE) return POSITIVE;
        return TOP;
    }

    @Override
    public StructuredRepresentation representation() {
        if (this == TOP) return Lattice.topRepresentation();
        if (this == BOTTOM) return Lattice.bottomRepresentation();
        if (this == POSITIVE) return new StringRepresentation(">= 0");
        if (this == STRICTLY_POSITIVE) return new StringRepresentation("> 0");
        if (this == NEGATIVE) return new StringRepresentation("<= 0");
        if (this == STRICTLY_NEGATIVE) return new StringRepresentation("< 0");
        if (this == ZERO) return new StringRepresentation("0");
        if (this == NON_ZERO) return new StringRepresentation("!= 0");
        return new StringRepresentation("?");
    }

    public boolean isAtLeastPositive(ExtendedSigns other) {
        return other == POSITIVE || other == STRICTLY_POSITIVE;
    }
    @Override
    public ExtendedSigns evalNonNullConstant(Constant constant, ProgramPoint pp, SemanticOracle oracle) {
        if (constant.getValue() instanceof Integer) {
            int v = (Integer) constant.getValue();
            if (v > 0) return STRICTLY_POSITIVE;
            else if (v == 0) return ZERO;
            else return STRICTLY_NEGATIVE;
        }
        return top();
    }

    private ExtendedSigns negate() {
        if (this == STRICTLY_NEGATIVE) return STRICTLY_POSITIVE;
        if (this == STRICTLY_POSITIVE) return STRICTLY_NEGATIVE;
        if (this == NEGATIVE) return POSITIVE;
        if (this == POSITIVE) return NEGATIVE;
        return this;
    }

    public ExtendedSigns fromNumberToExtendedSigns(int number) {
        if (number > 0) return STRICTLY_POSITIVE;
        if (number == 0) return ZERO;
        return STRICTLY_NEGATIVE;
    }

    

    @Override
    public ExtendedSigns evalUnaryExpression(UnaryOperator operator, ExtendedSigns arg, ProgramPoint pp, SemanticOracle oracle) {
        if (operator instanceof NumericNegation) return arg.negate();
        return arg;
    }

    public ExtendedSigns inverseLeftSign(ExtendedSigns left, ExtendedSigns right) {
        if(left == STRICTLY_POSITIVE) 
            return right == ZERO ? NEGATIVE : STRICTLY_NEGATIVE;
        if(left == STRICTLY_NEGATIVE)
            return right == ZERO ? POSITIVE : STRICTLY_NEGATIVE;
        // todo continue with other cases 
        return left.negate();
    }
    @Override
    public ValueEnvironment<ExtendedSigns> assumeBinaryExpression(ValueEnvironment<ExtendedSigns> environment,
			BinaryOperator operator,
			ValueExpression left,
			ValueExpression right,
			ProgramPoint src,
			ProgramPoint dest,
			SemanticOracle oracle) throws SemanticException {

        if(operator instanceof ComparisonLe){
            if(left instanceof Variable && right instanceof Constant){
                Variable x = (Variable) left;
                Constant y = (Constant) right;
                if(y.getValue() instanceof Integer){
                    ExtendedSigns xValue = environment.getState(x);
                    ExtendedSigns yValue = fromNumberToExtendedSigns((Integer) y.getValue());
                    System.err.println("xValue: " + xValue.representation() + " yValue: " + yValue);
                    if(xValue.isTop()) 
                        return environment;
                    System.err.println("Assuming x to be negative");
                    // todo : compare if the two values, if it's negative or extremly positive you could assume it's one of them only
                    // handle other cases 
                    return environment.putState(x,inverseLeftSign(xValue, yValue));
                }
            }
        }
        return BaseNonRelationalValueDomain.super.assumeBinaryExpression(environment, operator, left, right, src, dest, oracle);
    }

    @Override
    public ExtendedSigns evalBinaryExpression(BinaryOperator operator, ExtendedSigns left, ExtendedSigns right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (operator instanceof AdditionOperator) {
            if (left == ZERO) return right;
            if (right == ZERO) return left;
            if(left == TOP || right == TOP) return TOP;
            if(left == BOTTOM || right == BOTTOM) return BOTTOM;
            if (left == NEGATIVE && right == NEGATIVE) return NEGATIVE;
            if (left == POSITIVE && right == POSITIVE) return POSITIVE;
            if (left == STRICTLY_NEGATIVE && right == STRICTLY_NEGATIVE) return STRICTLY_NEGATIVE;
            if (left == STRICTLY_POSITIVE && right == STRICTLY_POSITIVE) return STRICTLY_POSITIVE;
            if (left == NEGATIVE && right == STRICTLY_NEGATIVE || left == STRICTLY_NEGATIVE && right == NEGATIVE) return NEGATIVE;
            if (left == POSITIVE && right == STRICTLY_POSITIVE || left == STRICTLY_POSITIVE && right == POSITIVE) return POSITIVE;
            return TOP;
        }
        if (operator instanceof SubtractionOperator) {
            ExtendedSigns rightNegated = right.negate();
            if (left == ZERO) return rightNegated;
            if (rightNegated == ZERO) return left;
            if(left == TOP || rightNegated == TOP) return TOP;
            if(left == BOTTOM || rightNegated == BOTTOM) return BOTTOM;
            if (left == NEGATIVE && rightNegated == NEGATIVE) return NEGATIVE;
            if (left == POSITIVE && rightNegated == POSITIVE) return POSITIVE;
            if (left == STRICTLY_NEGATIVE && rightNegated == STRICTLY_NEGATIVE) return STRICTLY_NEGATIVE;
            if (left == STRICTLY_POSITIVE && rightNegated == STRICTLY_POSITIVE) return STRICTLY_POSITIVE;
            if (left == NEGATIVE && rightNegated == STRICTLY_NEGATIVE || left == STRICTLY_NEGATIVE && rightNegated == NEGATIVE) return NEGATIVE;
            if (left == POSITIVE && rightNegated == STRICTLY_POSITIVE || left == STRICTLY_POSITIVE && rightNegated == POSITIVE) return POSITIVE;
            return TOP;
        }
        if (operator instanceof MultiplicationOperator) {
            if(left == BOTTOM|| right == BOTTOM) return BOTTOM;
            if (left == ZERO || right == ZERO) return ZERO;
            if (left == NEGATIVE) return right.negate();
            if (left == POSITIVE) return right;
            if (left == STRICTLY_NEGATIVE) return right.negate();
            if (left == STRICTLY_POSITIVE) return right;
            return TOP;
        }
        if (operator instanceof DivisionOperator) {
            if (right == ZERO) return BOTTOM;
            if(left == BOTTOM|| right == BOTTOM) return BOTTOM;
            if (left == ZERO) return ZERO;
            if (left == NEGATIVE) return right.negate();
            if (left == POSITIVE) return right;
            if (left == STRICTLY_NEGATIVE) return right.negate();
            if (left == STRICTLY_POSITIVE) return right;
            return TOP;
        }
        return BaseNonRelationalValueDomain.super.evalBinaryExpression(operator, left, right, pp, oracle);
    }
}
