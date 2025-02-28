package it.unive.lisa.tutorial;
import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

public class ConcreteValue implements BaseNonRelationalValueDomain<ConcreteValue> {
    public static final ConcreteValue BOTTOM = new ConcreteValue(Integer.MIN_VALUE), TOP = new ConcreteValue(Integer.MIN_VALUE);
    private final int value;
    private ConcreteValue(int value) {
        this.value = value;
    }
    @Override
    public ConcreteValue lubAux(ConcreteValue concreteValue) throws SemanticException {
        if(this.value == concreteValue.value)
            return concreteValue;
        else return top();
    }
    @Override
    public boolean lessOrEqualAux(ConcreteValue concreteValue) throws SemanticException {
        return this.value == concreteValue.value;
    }
    @Override
    public ConcreteValue top() {
        return TOP;
    }
    @Override
    public ConcreteValue bottom() {
        return BOTTOM;
    }
    @Override
    public StructuredRepresentation representation() {
        if(this.isBottom())
            return Lattice.bottomRepresentation();
        if(this.isTop())
            return Lattice.topRepresentation();
        return new StringRepresentation(String.valueOf(value));
    }
    @Override
    public ConcreteValue evalNonNullConstant(Constant constant, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if(constant.getValue() instanceof Integer)
            return new ConcreteValue((Integer) constant.getValue());
        return BaseNonRelationalValueDomain.super.evalNonNullConstant(constant, pp, oracle);
    }
    @Override
    public ConcreteValue evalBinaryExpression(BinaryOperator operator, ConcreteValue left, ConcreteValue right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if(operator instanceof AdditionOperator) {
            if(left.isTop() || right.isTop())
                return top();
            if(left.isBottom() || right.isBottom())
                return bottom();
            return new ConcreteValue(left.value + right.value);
        }
        return BaseNonRelationalValueDomain.super.evalBinaryExpression(operator, left, right, pp, oracle);
    }
}