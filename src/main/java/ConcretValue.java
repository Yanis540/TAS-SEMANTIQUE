import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

public class ConcretValue implements BaseNonRelationalValueDomain<ConcretValue>{
    private static final ConcretValue BOTTOM = new ConcretValue(Integer.MIN_VALUE),TOP = new ConcretValue(Integer.MAX_VALUE);
    private final int value;
    public ConcretValue(int value){
        this.value = value;
    }
    public ConcretValue top(){
        return TOP;
    }
    @Override
    public ConcretValue lubAux(ConcretValue other) throws SemanticException {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Unimplemented method 'lubAux'");
    }
    @Override
    public boolean lessOrEqualAux(ConcretValue other) throws SemanticException {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Unimplemented method 'lessOrEqualAux'");
    }
    @Override
    public ConcretValue bottom() {
        return BOTTOM;
    }
    @Override
    public StructuredRepresentation representation() {
        return new StringRepresentation(String.valueOf(value));
    }

    public ConcreteValue evalNonNullConstant(Constant constant,ProgramPoint p){
        
    }
}
