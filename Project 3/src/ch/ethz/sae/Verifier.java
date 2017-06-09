package ch.ethz.sae;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import apron.Interval;
import apron.ApronException;
import apron.Scalar;
import soot.jimple.Expr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.spark.SparkTransformer;
import soot.jimple.spark.pag.AllocNode;
import soot.jimple.spark.pag.Node;
import soot.jimple.spark.pag.PAG;
import soot.jimple.spark.sets.DoublePointsToSet;
import soot.jimple.spark.sets.P2SetVisitor;
import soot.Local;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.toolkits.graph.BriefUnitGraph;

public class Verifier {

    public static void main(String[] args) {
        if (args.length != 1) {
            System.err.println("Usage: java -classpath soot-2.5.0.jar:./bin ch.ethz.sae.Verifier <class to test>");
            System.exit(-1);
        }
        String analyzedClass = args[0];
        SootClass c = loadClass(analyzedClass);

        PAG pointsToAnalysis = doPointsToAnalysis(c);

        int weldAtFlag = 1;
        int weldBetweenFlag = 1;

        for (SootMethod method : c.getMethods()) {

            if (method.getName().contains("<init>")) {
                // skip constructor of the class
                continue;
            }
            Analysis analysis = new Analysis(new BriefUnitGraph(method.retrieveActiveBody()), c);
            analysis.run();
            
            if (!verifyWeldAt(method, analysis, pointsToAnalysis)) {
                weldAtFlag = 0;
            }
            if (!verifyWeldBetween(method, analysis, pointsToAnalysis)) {
                weldBetweenFlag = 0;
            }
        }
        
        // Do not change the output format
        if (weldAtFlag == 1) {
            System.out.println(analyzedClass + " WELD_AT_OK");
        } else {
            System.out.println(analyzedClass + " WELD_AT_NOT_OK");
        }
        if (weldBetweenFlag == 1) {
            System.out.println(analyzedClass + " WELD_BETWEEN_OK");
        } else {
            System.out.println(analyzedClass + " WELD_BETWEEN_NOT_OK");
        }
    }
    
    private static List<List> allConstructorArgsForVar(Local value, final Analysis fixPoint, PAG pointsTo){
        final List<List> results = new ArrayList<List>();
        ((DoublePointsToSet)pointsTo.reachingObjects((Local)value)).forall(new P2SetVisitor(){
                public void visit(Node node) {
                    JNewExpr newExpr = (JNewExpr)((AllocNode)node).getNewExpr();
                    results.add(fixPoint.constructorArgs.get(newExpr));
                }
            });
        return results;
    }

    private static boolean verifyWeldBetween(SootMethod method, Analysis fixPoint, PAG pointsTo) {
        for(Unit unit : method.getActiveBody().getUnits()){
            if(unit instanceof JInvokeStmt){
                InvokeExpr expr = ((JInvokeStmt)unit).getInvokeExpr();
                Value receiver = ((ValueBox)expr.getUseBoxes().get(0)).getValue();
                //Commented my attempt out. Remove it if yours works and mine isn't needed and/or working
    	        /*if(expr.getMethod().getName().equals("weldBetween")){
    	            Value left = expr.getArg(0);
    	            Value right = expr.getArg(1);
    	            AWrapper A = fixPoint.getFlowBefore(unit); //This should give the possible environments that the unit can receive? Hopefully.
    	            try {
    	                int cmpleft;
    	                if(left instanceof IntConstant) {
    	                    int l = ((IntConstant) left).value;
    	                    if(l == (Integer) receiver.getUseBoxes().get(0)) { //Compare left constant with first element of the receiving robot
    	                        cmpleft = 0;                                       // which should be left
    	                    } else if (l < (Integer) receiver.getUseBoxes().get(0)) {
    	                        cmpleft = -1;
    	                    } else {
    	                        cmpleft = 1;
    	                    }
    	                } else {
    	                cmpleft = A.get().getBound(fixPoint.man, ((Local) left).getName()).inf().cmp((Integer) receiver.getUseBoxes().get(0));
    	                } //compare inf of possible left local variable with receiver robot left, return false if it is smaller
    	                if (cmpleft == -1) {
    	                    return false;
    	                }
    	                //same for right
    	                int cmpright;
    	                if (right instanceof IntConstant) {
    	                    int r = ((IntConstant) right).value;
    	                    if(r == (Integer) receiver.getUseBoxes().get(1)) {
    	                        cmpright = 0;
    	                    } else if (r < ((Integer) receiver.getUseBoxes().get(1))) {
    	                        cmpright = -1;
    	                    } else {
    	                        cmpright = 1;
    	                    }
    	                } else {
    	                cmpright = A.get().getBound(fixPoint.man, ((Local) right).getName()).sup().cmp((Integer) receiver.getUseBoxes().get(1));
    	                }
    	                if (cmpright == 1) {
    	                    return false;
    	                }
    	            } catch (ApronException e) {
    	                return false;
    	            }
    	        }
    	        System.out.println("> "+allConstructorArgsForVar((Local)receiver, fixPoint, pointsTo));

    	    }

    	}
    	return true;*/
                if(expr.getMethod().getName().equals("weldBetween")){
                    try{
                        Interval leftPoint = fixPoint.coerceInterval(expr.getArg(0), fixPoint.getFlowBefore(unit).elem);
                        Interval rightPoint = fixPoint.coerceInterval(expr.getArg(1), fixPoint.getFlowBefore(unit).elem);
                        Interval weldRange = new Interval(fixPoint.min(fixPoint.scalarVal(leftPoint.inf()), fixPoint.scalarVal(rightPoint.inf())),
                                                          fixPoint.max(fixPoint.scalarVal(leftPoint.sup()), fixPoint.scalarVal(rightPoint.sup())));
                        for(List args : allConstructorArgsForVar((Local)receiver, fixPoint, pointsTo)){
                            int left = ((IntConstant)args.get(0)).value;
                            int right = ((IntConstant)args.get(1)).value;
                            if(!fixPoint.intervalContained(weldRange, new Interval(left, right))){
                                return false;
                            }
                        }
                    }catch(Exception ex){
                        ex.printStackTrace();
                    }
                }
            }

        }
        return true;
    }
    
    private static boolean verifyWeldAt(SootMethod method, Analysis fixPoint, PAG pointsTo) {
        for(Unit unit : method.getActiveBody().getUnits()){
            if(unit instanceof JInvokeStmt){
                InvokeExpr expr = ((JInvokeStmt)unit).getInvokeExpr();
                Value receiver = ((ValueBox)expr.getUseBoxes().get(0)).getValue();
                //Commentet my attempted solution out. Remove it if you think it's useless.
    	        /*if(expr.getMethod().getName().equals("weldAt")){
    	            Value point = expr.getArg(0);
    	            //Begin of untested part by me.
    	            AWrapper A = fixPoint.getFlowBefore(unit);
    	            if (point instanceof IntConstant) {
    	                int p = ((IntConstant) point).value;
    	                if (p < (Integer) receiver.getUseBoxes().get(0) || p > (Integer) receiver.getUseBoxes().get(1)) {
    	                    return false;
    	                }
    	            } else {
    	                try {
    	                if (A.get().getBound(fixPoint.man, ((Local) point).getName()).inf.cmp((Integer) receiver.getUseBoxes().get(0)) == -1) {
    	                    return false;
    	                }
    	                if(A.get().getBound(fixPoint.man, ((Local) point).getName()).sup.cmp((Integer) receiver.getUseBoxes().get(1)) == 1) {
    	                    return false;
    	                }
    	                } catch (ApronException e) {
    	                    return false;
    	                }
    	            }
    	            
                    System.out.println("> "+allConstructorArgsForVar((Local)receiver, fixPoint, pointsTo));    	            
    	        }
    	    }
    	}*/
                if(expr.getMethod().getName().equals("weldAt")){
                    try{
                        Interval weldPoint = fixPoint.coerceInterval(expr.getArg(0), fixPoint.getFlowBefore(unit).elem);
                        for(List args : allConstructorArgsForVar((Local)receiver, fixPoint, pointsTo)){
                            int left = ((IntConstant)args.get(0)).value;
                            int right = ((IntConstant)args.get(1)).value;
                            if(!fixPoint.intervalsOverlapping(weldPoint, new Interval(left, right))){
                                return false;
                            }
                        }
                    }catch(Exception ex){
                        ex.printStackTrace();
                    }
                }
            }
        }
        return true;
    }

    private static SootClass loadClass(String name) {
        SootClass c = Scene.v().loadClassAndSupport(name);
        c.setApplicationClass();
        return c;
    }

    // Performs Points-To Analysis
    private static PAG doPointsToAnalysis(SootClass c) {
        Scene.v().setEntryPoints(c.getMethods());

        HashMap<String, String> options = new HashMap<String, String>();
        options.put("enabled", "true");
        options.put("verbose", "false");
        options.put("propagator", "worklist");
        options.put("simple-edges-bidirectional", "false");
        options.put("on-fly-cg", "true");
        options.put("set-impl", "double");
        options.put("double-set-old", "hybrid");
        options.put("double-set-new", "hybrid");

        SparkTransformer.v().transform("", options);
        PAG pag = (PAG) Scene.v().getPointsToAnalysis();

        return pag;
    }

}
