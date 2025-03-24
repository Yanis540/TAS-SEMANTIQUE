package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.ScopeToken;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.FunctionalLattice;
import it.unive.lisa.analysis.lattices.InverseSetLattice;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.Environment;
import it.unive.lisa.analysis.nonrelational.NonRelationalDomain;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.program.cfg.statement.comparison.Equal;
import it.unive.lisa.program.cfg.statement.comparison.GreaterOrEqual;
import it.unive.lisa.program.cfg.statement.comparison.GreaterThan;
import it.unive.lisa.program.cfg.statement.comparison.LessOrEqual;
import it.unive.lisa.program.cfg.statement.comparison.LessThan;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.symbolic.value.*;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.*;
import it.unive.lisa.tutorial.NotEqualsDomain.SetOfIdentifiers;
import it.unive.lisa.tutorial.StrictUpperBounds.IdSet;
import it.unive.lisa.tutorial.TwoVariablesInequality.Inequality;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

public class TwoVariablesInequality 	extends
		// we reuse the value environment to simplify our implementation, but to do this we
		// have to make IdSet an NRVD even if we do not need it
		FunctionalLattice<TwoVariablesInequality, Identifier, TwoVariablesInequality.Inequality>
		// we make explicit that this is a value domain
		implements ValueDomain<TwoVariablesInequality> {

    public TwoVariablesInequality() {
		super(new Inequality(Collections.emptySet()).top());
	}

	public TwoVariablesInequality(Inequality lattice,Map<Identifier, Inequality> function) {
		super(lattice, function);
	}
    @Override
    public TwoVariablesInequality top() {
        return new TwoVariablesInequality(lattice.top(),null);
    }

    @Override
    public TwoVariablesInequality bottom() {
        return new TwoVariablesInequality(lattice.bottom(),null);
    }

    @Override
    public TwoVariablesInequality mk(Inequality lattice, Map<Identifier, Inequality> function) {
        return new TwoVariablesInequality(lattice, function); 
    }
    
    @Override
    public boolean knowsIdentifier(Identifier identifier) {
        return this.lattice.contains(identifier);
    }
    @Override
    public TwoVariablesInequality forgetIdentifiersIf(Predicate<Identifier> predicate) throws SemanticException {
         TwoVariablesInequality result = this;
        for (Identifier id : this.getKeys()) {
            if (predicate.test(id)) {
                result = result.forgetIdentifier(id);
            }
        }
        return result;
    }
    public TwoVariablesInequality lubAux(TwoVariablesInequality other ){
        if(other.isTop())
            return this;
        if(this.isTop())
            return other;
        if(this.isBottom())
            return other;
        if(other.isBottom())
            return this;
        TwoVariablesInequality result = this;
        for(Identifier id : this.getKeys()) {
            Inequality otherState = other.getState(id);
            if(otherState.isTop())
                result = result.putState(id, otherState);
            else {
                Inequality state = this.getState(id);
                Set<LinearInequality> inequalities = new HashSet<>(state.inequalities);
                inequalities.addAll(otherState.inequalities);
                Set<Identifier> variables = new HashSet<>(state.var());
                variables.addAll(otherState.var());
                Inequality newState = new Inequality(variables, variables.isEmpty());
                newState.setInequalities(inequalities);
                result = result.putState(id, newState);
            }
        }
        return result;
    }
    
    @Override
    public TwoVariablesInequality pushScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }

    @Override
    public TwoVariablesInequality popScope(ScopeToken scopeToken) throws SemanticException {
        return this;
    }

    public StructuredRepresentation representation() {
        return new StringRepresentation(lattice.toString());
    }


    public TwoVariablesInequality assume(
        ValueExpression expression,
        ProgramPoint src,
        ProgramPoint dest,
        SemanticOracle oracle) throws SemanticException {
        if (!(expression instanceof BinaryExpression)&&(!(expression instanceof UnaryExpression)))
			return this;
        BinaryExpression binaryExpression = (expression instanceof BinaryExpression)?(BinaryExpression) expression:(BinaryExpression)((UnaryExpression)expression).getExpression();
        if(!(binaryExpression.getOperator() instanceof ComparisonLt))
            return this;
            
        LinearInequality inequality = LinearInequality.toLinearInequality(binaryExpression);
        Set<Identifier> variables = new HashSet<>(inequality.var());
        Inequality newLattice = new Inequality(variables, variables.isEmpty());
        if(!variables.isEmpty())
            newLattice.setInequalities(Collections.singleton(inequality));
        return new TwoVariablesInequality(newLattice, this.function); 
    }
    public TwoVariablesInequality smallStepSemantics(ValueExpression valueExpression, ProgramPoint programPoint, SemanticOracle semanticOracle) throws SemanticException {
        // Handle different types of expressions
        return this;
    }
    
    
    public static class Inequality extends InverseSetLattice<Inequality, Identifier> {
        public Set<LinearInequality> inequalities;
        public Inequality(Set<Identifier> elements) {
            super(elements, elements.isEmpty());
            this.inequalities = new HashSet<>();
        }
        public void setInequalities(Set<LinearInequality> inequalities) {
            this.inequalities = new HashSet<>(inequalities);
        }
        public Inequality(Set<Identifier> elements, boolean isTop) {
            super(elements, isTop);
            this.inequalities = new HashSet<>();
        }
        public Set<Identifier> var() {
            Set<Identifier> result = new HashSet<>();
            for (LinearInequality inequality : inequalities) {
                result.addAll(inequality.var());
            }
            return result;
        }
         /**
         * Implémente l'opérateur de restriction πY défini dans l'article
         * πY(T) = {t ∈ T | var(t) ⊆ Y}
         */
        public Inequality restrictTo(Set<Identifier> variables) {
            Set<LinearInequality> restricted = new HashSet<>();
            for (LinearInequality inequality : inequalities) {
                if (variables.containsAll(inequality.var())) {
                    restricted.add(inequality);
                }
            }
            var t = new Inequality(variables, restricted.isEmpty());
            t.setInequalities(restricted);
            return t;
        }
        @Override
        public Inequality top() {
            return new Inequality(Collections.emptySet(), true);
        }

        @Override
        public Inequality bottom() {
            return new Inequality(Collections.emptySet(), false);
        }

     
        @Override
        public Inequality mk(Set<Identifier> set) {
            return new Inequality(set);
        }
        
    }

    /**
     * Classe représentant une inégalité linéaire ax + by ≤ c
    */
    public static class LinearInequality {
        // Coefficients des variables (ax + by)
        private Map<Identifier, Double> coefficients;
        // Constante c dans ax + by ≤ c
        private double constant;

        public LinearInequality(Map<Identifier, Double> coefficients, double constant) {
            this.coefficients = new HashMap<>(coefficients);
            this.constant = constant;
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
        /**
         * Convertit une expression de comparaison en inégalité linéaire
         */
        public static LinearInequality toLinearInequality(BinaryExpression comparison) throws SemanticException {
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
                if (Math.abs(coef) < 0.0001) continue; // Ignorer les coefficients proches de 0
                
                if (!first && coef > 0) sb.append(" + ");
                else if (!first) sb.append(" - ");
                else if (coef < 0) sb.append("-");
                
                if (Math.abs(Math.abs(coef) - 1.0) > 0.0001) {
                    sb.append(Math.abs(coef)).append("*");
                }
                
                sb.append(entry.getKey().getName());
                first = false;
            }
            
            sb.append(" ≤ ").append(constant);
            return sb.toString();
        }
    }

    @Override
    public TwoVariablesInequality assign(Identifier identifier, ValueExpression valueExpression, ProgramPoint pp,
            SemanticOracle oracle) throws SemanticException {
        return this;
    }
    private TwoVariablesInequality close() {
        TwoVariablesInequality result = this;
        for(Identifier domain : this.getKeys())
            for(Identifier codomain : this.getState(domain)) {
                Set<Identifier> value = new HashSet<>(result.getState(codomain).elements);
                value.add(domain);
                result = result.putState(codomain, new Inequality(value, false));
            }
        return result;
    }
    @Override
    public TwoVariablesInequality forgetIdentifier(Identifier identifier) throws SemanticException {
        TwoVariablesInequality result = this;
        if(result.getKeys().contains(identifier)) {
            result=result.putState(identifier, new Inequality(Collections.emptySet(), true));
        }
        for(Identifier id : result.getKeys())
            if(result.getState(id).elements.contains(identifier)) {
                Set<Identifier> s = new HashSet<>(result.getState(id).elements);
                s.remove(identifier);
                result = result.putState(id, new Inequality(s, s.isEmpty()));
            }
        return result;
    }

    @Override
    public Satisfiability satisfies(ValueExpression expression, ProgramPoint pp, SemanticOracle oracle)
            throws SemanticException {
        return Satisfiability.UNKNOWN;
    }


    @Override
    public Inequality stateOfUnknown(Identifier key) {
        return top().lattice;
    }


}
