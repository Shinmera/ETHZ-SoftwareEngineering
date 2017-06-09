package ch.ethz.sae;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import apron.Abstract1;
import apron.ApronException;
import apron.Environment;
import apron.Interval;
import apron.Linexpr1;
import apron.Manager;
import apron.Polka;
import apron.Scalar;
import soot.IntegerType;
import soot.Local;
import soot.SootClass;
import soot.SootField;
import soot.Unit;
import soot.Value;
import soot.jimple.BinopExpr;
import soot.jimple.DefinitionStmt;
import soot.jimple.IfStmt;
import soot.jimple.IntConstant;
import soot.jimple.ParameterRef;
import soot.jimple.Stmt;
import soot.jimple.internal.JAddExpr;
import soot.jimple.internal.JEqExpr;
import soot.jimple.internal.JGeExpr;
import soot.jimple.internal.JGtExpr;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JLeExpr;
import soot.jimple.internal.JLtExpr;
import soot.jimple.internal.JMulExpr;
import soot.jimple.internal.JNeExpr;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JSpecialInvokeExpr;
import soot.jimple.internal.JSubExpr;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.annotation.logic.Loop;
import soot.toolkits.graph.LoopNestTree;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.ForwardBranchedFlowAnalysis;
import soot.util.Chain;

// Implement your numerical analysis here.
public class Analysis extends ForwardBranchedFlowAnalysis<AWrapper> {

    private static final int WIDENING_THRESHOLD = 6;

    private HashMap<Unit, Counter> loopHeads, backJumps;

    private void recordIntLocalVars() {

        Chain<Local> locals = g.getBody().getLocals();

        int count = 0;
        Iterator<Local> it = locals.iterator();
        while (it.hasNext()) {
            JimpleLocal next = (JimpleLocal) it.next();
            if (next.getType() instanceof IntegerType)
                count += 1;
        }

        local_ints = new String[count];

        int i = 0;
        it = locals.iterator();
        while (it.hasNext()) {
            JimpleLocal next = (JimpleLocal) it.next();
            String name = next.getName();
            if (next.getType() instanceof IntegerType)
                local_ints[i++] = name;
        }
    }

    private void recordIntClassVars() {

        Chain<SootField> ifields = jclass.getFields();

        int count = 0;
        Iterator<SootField> it = ifields.iterator();
        while (it.hasNext()) {
            SootField next = it.next();
            if (next.getType() instanceof IntegerType)
                count += 1;
        }

        class_ints = new String[count];

        int i = 0;
        it = ifields.iterator();
        while (it.hasNext()) {
            SootField next = it.next();
            String name = next.getName();
            if (next.getType() instanceof IntegerType)
                class_ints[i++] = name;
        }
    }

    /* Builds an environment with integer variables. */
    public void buildEnvironment() {

        recordIntLocalVars();
        recordIntClassVars();

        String ints[] = new String[local_ints.length + class_ints.length];

        /* add local ints */
        for (int i = 0; i < local_ints.length; i++) {
            ints[i] = local_ints[i];
        }

        /* add class ints */
        for (int i = 0; i < class_ints.length; i++) {
            ints[local_ints.length + i] = class_ints[i];
        }

        env = new Environment(ints, reals);
    }

    /* Instantiate a domain. */
    private void instantiateDomain() {
        man = new Polka(true);
    }

    /* === Constructor === */
    public Analysis(UnitGraph g, SootClass jc) {
        super(g);

        this.g = g;
        this.jclass = jc;

        buildEnvironment();
        instantiateDomain();

        loopHeads = new HashMap<Unit, Counter>();
        backJumps = new HashMap<Unit, Counter>();
        for (Loop l : new LoopNestTree(g.getBody())) {
            loopHeads.put(l.getHead(), new Counter(0));
            backJumps.put(l.getBackJumpStmt(), new Counter(0));
        }
    }

    void run() {
        doAnalysis();
    }
    
    private Interval coerceInterval(Object o, Abstract1 elem) throws ApronException{
        if(o instanceof Local){
            return elem.getBound(man, ((Local)o).getName());
        }else if(o instanceof ParameterRef){
            Interval interval = new Interval();
            interval.setTop();
            return interval;
        }else if(o instanceof IntConstant){
            double value = ((IntConstant)o).value;
            return new Interval(value, value);
        }else{
            return null;
        }
    }
    
    // These are more convenient than Math.min/max.
    private double min(Double... ins){
        double min = ins[0];
        for(int i=1; i<ins.length; i++){
            if(ins[i]<min) min = ins[i];
        }
        return min;
    }
    
    private double max(Double... ins){
        double max = ins[0];
        for(int i=1; i<ins.length; i++){
            if(ins[i]>max) max = ins[i];
        }
        return max;
    }
    
    private Interval computeInequality(String condition, Interval left, Interval right){
        double left_i = scalarVal(left.inf());
        double left_s = scalarVal(right.sup());
        double right_i = scalarVal(left.inf());
        double right_s = scalarVal(right.sup());
        
        // If they don't overlap, set to bottom.
        if(left_s < right_i || right_s < left_i){
            Interval interval = new Interval();
            interval.setBottom();
            return interval;
        }
        
        /* */ if(condition.equals("==")){
            return new Interval(max(left_i, right_i), min(left_s, right_s));
        }else if(condition.equals("!=")){
            // Can't express, approximate by equating it to >.
            return new Interval(right_i+1, min(left_s, right_s));
        }else if(condition.equals("<=")){
            return new Interval(left_i, min(left_s, right_i));
        }else if(condition.equals("<")){
            return new Interval(left_i, min(left_s, right_i-1));
        }else if(condition.equals(">=")){
            return new Interval(right_i, min(left_s, right_s));
        }else if(condition.equals(">")){
            return new Interval(right_i+1, min(left_s, right_s));
        }else{
            return null;
        }
    }
    
    private String reverseInequality(String condition){
        /* */ if(condition.equals("==")){
            return "!=";
        }else if(condition.equals("!=")){
            return "==";
        }else if(condition.equals("<=")){
            return ">";
        }else if(condition.equals(">=")){
            return "<";
        }else if(condition.equals("<")){
            return ">=";
        }else if(condition.equals(">")){
            return "<=";
        }else{
            return null;
        }
    }
    
    // Not sure why toDouble is so complicated?
    private double scalarVal(Scalar scalar){
        double[] temp = new double[1];
        scalar.toDouble(temp, 0);
        return temp[0];
    }

    @Override
    protected void flowThrough(AWrapper inWrapper, Unit op,
                               List<AWrapper> fallOutWrappers, List<AWrapper> branchOutWrappers) {
        System.out.println("Flowing through "+op);
        try{
            Stmt s = (Stmt) op;
            Abstract1 elem = inWrapper.get();
            AWrapper out = new AWrapper(new Abstract1(man, elem));
            out.man = man;
            AWrapper outBranch = new AWrapper(new Abstract1(man, elem));
            outBranch.man = man;

            if (s instanceof JInvokeStmt){
                Value expr = ((JInvokeStmt)s).getInvokeExpr();
                if(expr instanceof JSpecialInvokeExpr){
                    System.out.println("> "+((JSpecialInvokeExpr)expr).getBase());
                }
            }else if (s instanceof DefinitionStmt && isIntValue(((DefinitionStmt)s).getLeftOp())) {
                DefinitionStmt sd = (DefinitionStmt)s;
                String var = ((Local)sd.getLeftOp()).getName();
                Value rhs = sd.getRightOp();
           
                Interval coeff = null;
                /* */ if(rhs instanceof IntConstant){
                    coeff = coerceInterval(rhs, elem);
                }else if(rhs instanceof Local){
                    coeff = coerceInterval(rhs, elem);
                }else if(rhs instanceof ParameterRef){
                    coeff = coerceInterval(rhs, elem);
                }else{
                    Interval left = coerceInterval(((BinopExpr)rhs).getOp1(), elem);
                    Interval right = coerceInterval(((BinopExpr)rhs).getOp2(), elem);
                    double left_i = scalarVal(left.inf());
                    double left_s = scalarVal(right.sup());
                    double right_i = scalarVal(left.inf());
                    double right_s = scalarVal(right.sup());
                    
                    if(rhs instanceof JMulExpr){
                        coeff = new Interval(
                                min(left_i*right_i, left_i*right_s, left_s*right_i, left_s*right_s),
                                max(left_i*right_i, left_i*right_s, left_s*right_i, left_s*right_s));
                    }else if(rhs instanceof JSubExpr){
                        coeff = new Interval(left_i-right_i, left_s-right_s);
                    }else if(rhs instanceof JAddExpr){
                        coeff = new Interval(left_i+right_i, left_s+right_s);
                    }else{
                        throw new Exception("Unsupported right hand side: "+rhs);
                    }
                }
                Linexpr1 expr = new Linexpr1(elem.getEnvironment());
                expr.setCst(coeff);
                out.get().assign(man, new String[]{var}, new Linexpr1[]{expr}, elem);
                
                fallOutWrappers.add(out);
            } else if (s instanceof JIfStmt) {
                IfStmt ifStmt = (JIfStmt) s;
                BinopExpr condition = (BinopExpr)ifStmt.getCondition();
                Value left = condition.getOp1();
                Value right = condition.getOp2();
                String inequality = null;
                
                /* */ if(condition instanceof JEqExpr){
                    inequality = "==";
                }else if(condition instanceof JNeExpr){
                    inequality = "!=";
                }else if(condition instanceof JGeExpr){
                    inequality = ">=";
                }else if(condition instanceof JGtExpr){
                    inequality = ">";
                }else if(condition instanceof JLeExpr){
                    inequality = "<=";
                }else if(condition instanceof JLtExpr){
                    inequality = "<";
                }else{
                    throw new Exception("Unsupported condition: "+condition);
                }

                Interval left_int = coerceInterval(left, elem);
                Interval right_int = coerceInterval(right, elem);
                
                // Compute for left hand side if it is a variable
                Linexpr1 expr;
                if(left instanceof Local){
                    expr = new Linexpr1(elem.getEnvironment());
                    expr.setCst(computeInequality(inequality, left_int, right_int));
                    outBranch.get().assign(man, new String[]{((Local)left).getName()}, new Linexpr1[]{expr}, elem);
                    // Compute the inverse for the fallOut.
                    expr = new Linexpr1(elem.getEnvironment());
                    expr.setCst(computeInequality(reverseInequality(inequality), left_int, right_int));
                    out.get().assign(man, new String[]{((Local)left).getName()}, new Linexpr1[]{expr}, elem);
                }
                
                // Compute for right hand side if it is a variable.
                // This is the same as left-hand side if we invert the inequality and swap order accordingly.
                if(right instanceof Local){
                    expr = new Linexpr1(elem.getEnvironment());
                    expr.setCst(computeInequality(reverseInequality(inequality), right_int, left_int));
                    outBranch.get().assign(man, new String[]{((Local)right).getName()}, new Linexpr1[]{expr}, elem);
                    // Compute the inverse for the fallOut.
                    expr = new Linexpr1(elem.getEnvironment());
                    expr.setCst(computeInequality(inequality, right_int, left_int));
                    out.get().assign(man, new String[]{((Local)right).getName()}, new Linexpr1[]{expr}, elem);
                }
            }
            
            for(AWrapper wrapper : fallOutWrappers){
                wrapper.copy(out);
            }
            
            for(AWrapper wrapper : branchOutWrappers){
                wrapper.copy(outBranch);
            }
        }catch(Exception ex){
            ex.printStackTrace();
        }
    }

    @Override
    protected void copy(AWrapper source, AWrapper dest) {
        try {
            dest.set(new Abstract1(man, source.get()));
        } catch (ApronException e) {
            e.printStackTrace();
        }
    }

    @Override
    protected AWrapper entryInitialFlow() {
        Abstract1 top = null;
        try {
            top = new Abstract1(man, env);
        } catch (ApronException e) {
        }
        return new AWrapper(top);
    }

    private static class Counter {
        int value;

        Counter(int v) {
            value = v;
        }
    }

    @Override
    protected void merge(Unit succNode, AWrapper w1, AWrapper w2, AWrapper w3) {
        Counter count = loopHeads.get(succNode);

        Abstract1 a1 = w1.get();
        Abstract1 a2 = w2.get();
        Abstract1 a3 = null;

        try {
            if (count != null) {
                ++count.value;
                if (count.value < WIDENING_THRESHOLD) {
                    a3 = a1.joinCopy(man, a2);
                } else {
                    a3 = a1.widening(man, a2);
                }
            } else {
                a3 = a1.joinCopy(man, a2);
            }
            w3.set(a3);
        } catch (Exception e) {
            System.out.println(e);
        }
    }

    @Override
    protected void merge(AWrapper src1, AWrapper src2, AWrapper trg) {

        Abstract1 a1 = src1.get();
        Abstract1 a2 = src2.get();
        Abstract1 a3 = null;

        try {
            a3 = a1.joinCopy(man, a2);
        } catch (ApronException e) {
            e.printStackTrace();
        }
        trg.set(a3);
    }

    @Override
    protected AWrapper newInitialFlow() {
        Abstract1 bot = null;

        try {
            bot = new Abstract1(man, env, true);
        } catch (ApronException e) {
        }
        AWrapper a = new AWrapper(bot);
        a.man = man;
        return a;

    }

    public static final boolean isIntValue(Value val) {
        return val.getType().toString().equals("int")
            || val.getType().toString().equals("short")
            || val.getType().toString().equals("byte");
    }


    public static Manager man;
    public static Environment env;
    public UnitGraph g;
    public String local_ints[]; // integer local variables of the method
    public static String reals[] = { "x" };
    public SootClass jclass;
    private String class_ints[]; // integer class variables where the method is
    // defined
}
