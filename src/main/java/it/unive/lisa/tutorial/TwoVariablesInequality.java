package it.unive.lisa.tutorial;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.FunctionalLattice;
import it.unive.lisa.analysis.lattices.InverseSetLattice;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.symbolic.value.BinaryExpression;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.UnaryExpression;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLt;
import it.unive.lisa.util.datastructures.regex.TopAtom;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

public class TwoVariablesInequality 	
		
		implements ValueDomain<TwoVariablesInequality> {
    public static final TwoVariablesInequality TOP = new TwoVariablesInequality(true);
    public static final TwoVariablesInequality BOTTOM = new TwoVariablesInequality(false);
    public boolean top=false,bottom=false;
    private TwoVariablesInequality(boolean top) {
        if(top)
            this.top = true;
        else 
            this.bottom = true;
        this.inequalities = new HashSet<>();
	}
    public TwoVariablesInequality(Set<LinearInequality>inequalities) {
        if(inequalities.isEmpty())
            this.top = true;
        this.inequalities = new HashSet<>(removeDuplicates(inequalities));
         
	}


    public TwoVariablesInequality top() {
        return TOP;
    }
    public boolean isTop(){
        return this.top;
    }
    public boolean isBottom(){
        return this.bottom;
    }

    public TwoVariablesInequality bottom() {
        return BOTTOM;
    }

    public boolean knowsIdentifier(Identifier identifier) {
        return false; 
    }
    public TwoVariablesInequality forgetIdentifiersIf(Predicate<Identifier> predicate) throws SemanticException {
        return this;
    }
    public TwoVariablesInequality pushScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }
    public TwoVariablesInequality popScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }

    public StructuredRepresentation representation() {
        if(isTop())
            return new StringRepresentation("TOP");
        if(isBottom())
            return new StringRepresentation("BOTTOM");
        return new StringRepresentation(toString());
    }
   
    @Override
    public TwoVariablesInequality assume(
        ValueExpression expression,
        ProgramPoint src,
        ProgramPoint dest,
        SemanticOracle oracle) throws SemanticException {
        if (!(expression instanceof BinaryExpression))
            return this;

        
        BinaryExpression binaryExpression = (expression instanceof BinaryExpression)?(BinaryExpression) expression:(BinaryExpression)((UnaryExpression)expression).getExpression();
        if(!(binaryExpression.getOperator() instanceof ComparisonLt))
            return this;
            
        LinearInequality inequality = LinearInequality.fromBinaryExpression(binaryExpression);
        Set<LinearInequality> res = new HashSet<>(this.inequalities);
        if(inequality!=null){
            res.add(inequality);
        }
        System.out.println("Assuming: " + inequality.toString());
        System.out.println("Having: " + toString());
        // return bottom();
        return new TwoVariablesInequality(removeDuplicates(res));
    }

    public Set<LinearInequality> removeDuplicates(Set<LinearInequality> inequalities) {
        // GO TRHOW the inequalities and remove the equivalent ones 
        Set<LinearInequality> result = new HashSet<>();
        for (LinearInequality inequality : inequalities) {
            boolean isEquivalent = false;
            for (LinearInequality existingInequality : result) {
                if (inequality.equals(existingInequality)) {
                    isEquivalent = true;
                    break;
                }
            }
            if (!isEquivalent) {
                result.add(inequality);
            }
        }
        return result;
    }
    public TwoVariablesInequality smallStepSemantics(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        // Handle different types of expressions
        return this;
    }
    @Override
    public boolean lessOrEqual(TwoVariablesInequality other) throws SemanticException {
        return false;
    }
    @Override
    public TwoVariablesInequality lub(TwoVariablesInequality other) throws SemanticException {
        // union est l'intersection des deux ensembles 
        if(isTop())
            return other;
        if(other.isTop())
            return this;
        if(isBottom())
            return other;
        if(other.isBottom())
            return this;
         // Créer un nouvel ensemble qui est l'union des deux ensembles d'inégalités
        Set<LinearInequality> unionInequalities = new HashSet<>(this.inequalities);
        unionInequalities.addAll(other.inequalities);
        
        return new TwoVariablesInequality(unionInequalities);
    }
    @Override
    public TwoVariablesInequality glb(TwoVariablesInequality other) throws SemanticException {
        if (isTop()) return other;
        if (other.isTop()) return this;
        if (isBottom() || other.isBottom()) return BOTTOM;
        Set<LinearInequality> result = new HashSet<>(this.inequalities);
        result.addAll(other.inequalities);
        return new TwoVariablesInequality(result);
    }

    
    public Set<Identifier> vars() {
        Set<Identifier> result = new HashSet<>();
        for (LinearInequality inequality : inequalities) {
            result.addAll(inequality.var());
        }
        return result;
    }
    public String toString(){
        StringBuilder sb = new StringBuilder();
        sb.append("{");
        boolean first = true;
        
        for(LinearInequality inequality : inequalities) {
            if(!first)
                sb.append(", ");
            sb.append(inequality.toString());
            first = false;
        }
        sb.append("}");
        return sb.toString();
    }


     /**
     * Implémente l'opérateur de restriction πY défini dans l'article
     * πY(T) = {t ∈ T | var(t) ⊆ Y}
     */
    public Set<LinearInequality> restrictTo(Set<Identifier> variables) {
        Set<LinearInequality> restricted = new HashSet<>();
        for (LinearInequality inequality : inequalities) {
            if (variables.containsAll(inequality.var())) {
                restricted.add(inequality);
            }
        }
        return restricted;
    }
    public Set<LinearInequality> inequalities=new HashSet<>();


    /**
     * Classe représentant une inégalité linéaire ax + by ≤ c
    */
    public static class LinearInequality {
        // Coefficients des variables (ax + by)
        public Map<Identifier, Double> coefficients;
        public boolean lessOrEqual = false;
        // Constante c dans ax + by ≤ c
        private double constant;

        public LinearInequality(Map<Identifier, Double> coefficients, double constant) {
            this.coefficients = new HashMap<>(coefficients);
            this.constant = constant;
        }
        public void setLessOrEqual(boolean lessOrEqual) {
            this.lessOrEqual = lessOrEqual;
        }

        /**
         * Implémente la fonction var(ax + by ≤ c) comme définie dans l'article
         */
        public Set<Identifier> var() {
            Set<Identifier> result = new HashSet<>();
            for (Map.Entry<Identifier, Double> entry : coefficients.entrySet()) {
                double coef = entry.getValue();
                if(coef != 0)
                    result.add(entry.getKey());
            }
            return result;
        }
        public boolean equals(LinearInequality other) {
            if (this == other) return true;
            return coefficients.equals(other.coefficients) && constant == other.constant;
        }
        /**
         * Convertit une expression de comparaison en inégalité linéaire
         */
        public static LinearInequality fromBinaryExpression(BinaryExpression comparison) throws SemanticException {
            // Par défaut, on suppose que la forme est left OP right
            // On veut normaliser en ax + by ≤ c
            if(!(comparison.getOperator() instanceof ComparisonLt))
                throw new SemanticException("Unsupported expression: " + comparison);

            SymbolicExpression left = comparison.getLeft();
            SymbolicExpression right = comparison.getRight();
            
            // Extraire les coefficients et constantes
            Map<Identifier, Double> coefficients = new HashMap<>();
            double constant = 0.0;
            if(right instanceof Constant) {
                // On veut que la constante soit à droite
               constant = ((Integer)((Constant) right).getValue());
            }
            // extract a, x and b from left and c from left 
            if (left instanceof BinaryExpression) {
                BinaryExpression leftExpr = (BinaryExpression) left;
                if (leftExpr.getOperator() instanceof AdditionOperator) {
                    // try extract a and b, x and y
                    SymbolicExpression ax = leftExpr.getLeft();
                    SymbolicExpression by = leftExpr.getRight();
                    if(ax instanceof BinaryExpression ){
                        BinaryExpression axExpr = (BinaryExpression) ax;
                        if(axExpr.getOperator() instanceof MultiplicationOperator) {
                            SymbolicExpression a = axExpr.getLeft();
                            SymbolicExpression x = axExpr.getRight();
                            if(a instanceof Constant && x instanceof Identifier) {
                                coefficients.put((Identifier) x, ((Integer)((Constant) a).getValue()).doubleValue());
                            } else {
                                throw new SemanticException("Unsupported expression: " + ax);
                            }
                        } else {
                            throw new SemanticException("Unsupported expression: " + ax);
                        }
                    }
                    if(by instanceof BinaryExpression ){
                        BinaryExpression byExpr = (BinaryExpression) by;
                        if(byExpr.getOperator() instanceof MultiplicationOperator) {
                            SymbolicExpression b = byExpr.getLeft();
                            SymbolicExpression y = byExpr.getRight();
                            if(b instanceof Constant && y instanceof Identifier) {
                                coefficients.put((Identifier) y, ((Integer)((Constant) b).getValue()).doubleValue());
                            } else {
                                throw new SemanticException("Unsupported expression: " + by);
                            }
                        } else {
                            throw new SemanticException("Unsupported expression: " + by);
                        }
                    }
                    
                }
            }
            return new LinearInequality(coefficients, constant);
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            boolean first = true;
            
            for (Map.Entry<Identifier, Double> entry : coefficients.entrySet()) {
                double coef = entry.getValue();
                if (!first && coef > 0) sb.append(" + ");
                else if (!first) sb.append(" - ");
                else if (coef < 0) sb.append("-");
                
                if (Math.abs(Math.abs(coef) - 1.0) > 0.0001) {
                    sb.append(Math.abs(coef)).append("*");
                }
                
                sb.append(entry.getKey().getName());
                first = false;
            }
            
            sb.append(" < ").append(constant);
            return sb.toString();
        }
    }

    public TwoVariablesInequality assign(Identifier identifier, ValueExpression valueExpression, ProgramPoint pp,
            SemanticOracle oracle) throws SemanticException {
        return this;
    }
    public TwoVariablesInequality close() {
        TwoVariablesInequality result = this;
       
        return result;
    }
    public TwoVariablesInequality forgetIdentifier(Identifier identifier) throws SemanticException {
        TwoVariablesInequality result = this;
        
        return result;
    }

    public Satisfiability satisfies(ValueExpression expression, ProgramPoint pp, SemanticOracle oracle)
            throws SemanticException {
        return Satisfiability.UNKNOWN;
    }




}
