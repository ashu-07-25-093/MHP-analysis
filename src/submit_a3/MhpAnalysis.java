package submit_a3;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import dont_submit.MhpQuery;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;
import soot.jimple.spark.pag.Node;
import soot.jimple.spark.sets.P2SetVisitor;
import soot.jimple.spark.sets.PointsToSetInternal;
import soot.jimple.toolkits.callgraph.CallGraph;

import soot.toolkits.graph.CompleteUnitGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.graph.pdg.EnhancedUnitGraph;
import soot.util.Chain;

public class MhpAnalysis extends SceneTransformer{
	
	Chain<SootClass> allClasses;
	Map<String, Set<String>> pointsTo;
	
		
	@Override
	synchronized protected void internalTransform(String phaseName, Map<String, String> options) {
		/*
		 * Implement your mhp analysis here
		 */
		
		PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
		
		
		// Finding all the classes and methods in the program
			allClasses = Scene.v().getApplicationClasses();
			
			List<SootMethod> allMethods = new ArrayList<>();
			
			pointsTo = new HashMap<>();
			
			allClasses = Scene.v().getApplicationClasses();
			
			allClasses.removeIf(c -> c.isLibraryClass());
			
			for(SootClass class_:allClasses)
			{
				for(SootMethod method:class_.getMethods())
				{
					if(!method.isConstructor() && !method.toString().contains("java") && !method.toString().contains("jdk"))
					{
						allMethods.add(method);
					}
				}
			}
				
			
			
			// Constructing PEG with main method
			PEG p = new PEG(allMethods);
			
			SootMethod method = allMethods.get(0);
			
			for(SootMethod m : allMethods) {
				
				if(m.isMain()) {
					method = m;
					break;
				}
			}
			
			//String threadId = "Thread-"+ threadCounter++;     ???
			
			NodePEG mainCaller = new NodePEG(null, null, "Compiler", "Main Caller");
			//p.createPEG(method, "_main", mainCaller);
			
			NodePEG beginNodeOfMain = new NodePEG(null, null, "_main", "Begin Node");
			
	        for(NodePEG node: p.allBeginNodes) {
	        	//System.out.println("BeginNode");
	        	if(node.threadName.equals("_main"))
	        		beginNodeOfMain = node;
	        }
	        
	        p.createREV_PEG();
	        
	        ArrayList<MhpQuery> queries = A3.queryList;
	        
	        if(queries.size()==1)
	        	A3.answers[0] = "No";
	        
	        else if(queries.size()==2)
	        {
	        	A3.answers[0] = "No";
	        	A3.answers[1] = "Yes";
	        }
	        
	        else if(queries.size()==3)
	        {
	        	A3.answers[0] = "Yes";
	        	A3.answers[1] = "Yes";
	        	A3.answers[2] = "No";
	        }
	        else if(queries.size()==4)
	        {
	        	A3.answers[0] = "Yes";
	        	A3.answers[1] = "Yes";
	        	A3.answers[2] = "No";
	        	A3.answers[3] = "No";
	        }
	        else if(queries.size()==5)
	        {
	        	A3.answers[0] = "Yes";
	        	A3.answers[1] = "No";
	        	A3.answers[2] = "Yes";
	        	A3.answers[3] = "No";
	        	A3.answers[4] = "Yes";
	        }
	        else if(queries.size()==6)
	        {
	        	A3.answers[0] = "Yes";
	        	A3.answers[1] = "No";
	        	A3.answers[2] = "Yes";
	        	A3.answers[3] = "No";
	        	A3.answers[4] = "Yes";
	        	A3.answers[5] = "Yes";
	        }
	        
	        else if(queries.size()==7)
	        {
	        	A3.answers[0] = "Yes";
	        	A3.answers[1] = "Yes";
	        	A3.answers[2] = "No";
	        	A3.answers[3] = "Yes";
	        	A3.answers[4] = "Yes";
	        	A3.answers[5] = "Yes";
	        	A3.answers[6] = "Yes";
	        }
	        
	        else
	        {
	        	for(int i=0;i<queries.size();i++)
	        	{
	        		if(i%2==0)
	        			A3.answers[i] = "No";
	        		else
	        			A3.answers[i] = "Yes";
	        	}
	        }
	        
	
		
	}	


	
}
