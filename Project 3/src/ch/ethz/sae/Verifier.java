package ch.ethz.sae;

import java.util.HashMap;
import java.util.Iterator;

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

    private static boolean verifyWeldBetween(SootMethod method, Analysis fixPoint, PAG pointsTo) {
    	for(Unit unit : method.getActiveBody().getUnits()){
    	    if(unit instanceof JInvokeStmt){
    	        InvokeExpr expr = ((JInvokeStmt)unit).getInvokeExpr();
                Value receiver = ((ValueBox)expr.getUseBoxes().get(0)).getValue();
    	        if(expr.getMethod().getName().equals("weldBetween")){
    	            Value left = expr.getArg(0);
    	            Value right = expr.getArg(1);
    	            
    	        }
    	    }
    	}
        return false;
    }

    private static boolean verifyWeldAt(SootMethod method, Analysis fixPoint, PAG pointsTo) {
        for(Unit unit : method.getActiveBody().getUnits()){
    	    if(unit instanceof JInvokeStmt){
    	        InvokeExpr expr = ((JInvokeStmt)unit).getInvokeExpr();
                Value receiver = ((ValueBox)expr.getUseBoxes().get(0)).getValue();
    	        if(expr.getMethod().getName().equals("weldAt")){
    	            Value point = expr.getArg(0);
    	            ((DoublePointsToSet)pointsTo.reachingObjects((Local)receiver)).forall(new P2SetVisitor(){
                        public void visit(Node node) {
                            JNewExpr newExpr = (JNewExpr)((AllocNode)node).getNewExpr();
                            int inf = ((IntConstant)((ValueBox)newExpr.getUseBoxes().get(0)).getValue()).value;
                            int sup = ((IntConstant)((ValueBox)newExpr.getUseBoxes().get(1)).getValue()).value;
                            System.out.println("["+inf+","+sup+"]");
                        }
    	            });
    	        }
    	    }
    	}
        return false;
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
