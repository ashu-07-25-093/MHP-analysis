package submit_a3;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;

import com.google.common.collect.Sets;

import soot.Local;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.ExitMonitorStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.spark.sets.P2SetVisitor;
import soot.jimple.spark.sets.PointsToSetInternal;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;
import soot.jimple.spark.pag.Node;

class NodePEG
{
	Set<String> _obj;
	Unit unit;
	String threadName;
	String nodeType;
	
	Set<NodePEG> m;
	Set<NodePEG> out_m;
	
	NodePEG(Set<String> obj, Unit u, String tName, String nType)
	{
		this._obj = obj;
		this.unit = u;
		this.threadName = tName;
		this.nodeType = nType;
		
		m = new HashSet<>();
		out_m = new HashSet<>();
	}
	
//	void printNode()
//	{
//		System.out.println("receiver : "+_obj+".......unit : "+unit+".........threadName : "+threadName+"......nodeType : "+nodeType);
//	}	
}
class Edge
{
	NodePEG targetNode;
	String edgeType;
	
	Edge(NodePEG tNode, String eType)
	{
		this.targetNode = tNode;
		this.edgeType = eType;
	}
}

class PEG
{
	Map<NodePEG, Set<Edge>> peg;
	Map<NodePEG, Set<Edge>> rev_peg;
	
	List<SootMethod> _allMethods;
	List<NodePEG> allBeginNodes = new ArrayList<>();
	
	static int threadId = 0;
	
	PEG(List<SootMethod> allMethods)
	{
		_allMethods = allMethods;
		peg = new HashMap<>();
		rev_peg = new HashMap<>();
	}
	
	
	String getThreadId(SootMethod method)
	{
		if(method.isMain())
			return "_main";
		
		threadId++;
		return "T" + threadId;
	}
	
	Set<String> findPointsToList(Local l){
		
		PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
		PointsToSet ptSet = pta.reachingObjects(l);
		PointsToSetInternal pti = (PointsToSetInternal)ptSet;
		
		
		Set<String> p2set = new HashSet<>();
		P2SetVisitor vis = new P2SetVisitor(){

            @Override
            public void visit(Node n){
             /* Do something with node n*/
            	String str = new String(""+n.getType()+n.getNumber());
            	//System.out.println(str);
            	p2set.add(str);
         	    //System.out.println("n: "+n.getType()+n.getNumber());
	     
            }
    	};
    	pti.forall(vis);
    	
    	return p2set;
	}
	
	void traversal(NodePEG src)
	{
		Set<NodePEG> vis = new HashSet<>();
		
		vis.add(src);
		
		Queue<NodePEG> q = new LinkedList<>();
		q.add(src);
		
		while(!q.isEmpty())
		{
			NodePEG node = q.poll();
			
			Set<Edge> neighbours = peg.get(node);
			
			for(Edge e:neighbours)
			{
				if(!vis.contains(e))
				{
					q.add(e.targetNode);
				}
			}
		}
	}
	
	Set<NodePEG> setUnion(Set<NodePEG> s1, Set<NodePEG> s2)
	{
		Set<NodePEG> res = new HashSet<>();
		res = Sets.union(s1, s2);
		
		return res;
	}
	
	Set<NodePEG> setDiff(Set<NodePEG> s1, Set<NodePEG> s2)
	{
		Set<NodePEG> res = new HashSet<>();
		
		for(NodePEG node:s1)
		{
			if(!s2.contains(node))
				res.add(node);
		}
		return res;
	}
	
		//return waiting predecessors of node
		NodePEG waitingPred(NodePEG node){
			
			//traverse predecessor graph to check if it has node with "waiting" property
			Set<Edge> edges = rev_peg.get(node);
			
			for(Edge e:edges)
			{
				if(e.targetNode.nodeType.equals("waiting"))
				{
					return e.targetNode;
				}
			}
			
			return null;
			
		}
		
		//returns start predecessor of node
		Set<NodePEG> startPredOfNode(NodePEG node){
			
			Set<NodePEG> startPredNodes = new HashSet<>();
			
			//traverse predecessor graph to check if it has node with "start" property
			for(Edge e: rev_peg.get(node))
			{
				if(e.targetNode.nodeType.equals("start")) {
					startPredNodes.add(e.targetNode);
				}
			}
			return startPredNodes;
		}
		
		//returns notify successors of node 
		Set<NodePEG> getNotifySuccs(NodePEG node){
			
			Set<NodePEG> notifySuccs = new HashSet<>();
			
			//check if there is waiting node in M(n) set
			for(NodePEG parallelNode: node.m) {
				
				//if waiting node found
				if(parallelNode.nodeType.equals("waititng")) {
					
					//find its notifiedEntryNode
					NodePEG notifiedEntry = null;
					
					//successor of waiting node is notified-entry node
					Set<Edge> succs = peg.get(parallelNode);
					
					if(succs.iterator().hasNext())
						notifiedEntry = succs.iterator().next().targetNode;
					
					//if notified-entry found, check if intersection is not null of p2set of waiting and notifedentry node
					if(notifiedEntry.nodeType.equals("notifiedentry")) {
						
						if(node._obj!=null) {
							Set<NodePEG> intersect = new HashSet<>();
						}
					}
				}
			}
			return notifySuccs;
		}
	
		boolean _hasIntersection(Set<String> s1, Set<String> s2) {
			
	    	for(String s: s1) {
	    		if(s2.contains(s))
	    			return true;
	    	}
	    	return false;
	    }
	    
	    Set<NodePEG> _getIntesectOfPEGNodes(Set<NodePEG> s1, Set<NodePEG> s2) {
	    	
	    	Set<NodePEG> intersect = new HashSet<>();
	    	
	    	intersect = Sets.intersection(s1, s2);

	    	return intersect;
	    }
	    
	    
	    Set<NodePEG> findGENOfNotifyAll(NodePEG node){
	    	
	    	Set<NodePEG> genNotifyAllNodes = new HashSet<>();
	    	
	    	if(node.nodeType.equals("notifiedentry")) 
	    	{
	    		Set<NodePEG> pegNodes = peg.keySet();
	    		
	    		for(NodePEG _n:pegNodes) 
	    		{
	    			//check if m is notified-entry node and has common objects
	    			if(_n.nodeType.equals("notifiedentry") && _hasIntersection(_n._obj,node._obj)) {
	    				
	    				//check if waiting predecessors of m is in M set of n
	    				if(waitingPred(node).m.contains(waitingPred(_n))) 
	    				{
	    					Set<NodePEG> rs = peg.keySet();
	    					
	    					for(NodePEG r: rs) 
	    					{
	    						if(r.nodeType.equals("notifyall")) {
	    							
	    							//if r is M set of both the waiting predecessors of m and n, then add m to list
	    							Set<NodePEG> intersect = _getIntesectOfPEGNodes(waitingPred(_n).m, waitingPred(node).m);
	    							
	    							if(intersect.contains(r)) {
	    								genNotifyAllNodes.add(_n);
	    							}
	    						}
	    					}
	    				}
	    			}
	    		}
	    	}
	    	return genNotifyAllNodes;
	    }
	
	  //return all nodes of thread
	Set<NodePEG> allThreadNodes(String threadName){
    	
       	Set<NodePEG> threadNodes = new HashSet<>();
       	Set<NodePEG> pegNodes = peg.keySet();
       	
        for(NodePEG node: pegNodes)
        {	
            if(node.threadName.equals(threadName))
            	threadNodes.add(node);
        }

        return threadNodes;
    }
	
	Set<NodePEG> _waitingNodesWithSameObj(String obj) {
    	
    	Set<NodePEG> waitingNodes_w_same_obj = new HashSet<>();
    	
    	for(NodePEG node : peg.keySet())
    	{
    		if(node.nodeType.equals("waiting") && node._obj.contains(obj)) 
    			waitingNodes_w_same_obj.add(node);
    	}
    
    	return waitingNodes_w_same_obj;
    	
    }
	
	Set<NodePEG> findKillSETOfNode(NodePEG node)
	{
		//if n is join with single object then we can kill all the statements of thread
		Stmt stmt = (Stmt)node.unit;
		
    	if(stmt.containsInvokeExpr() && stmt.getInvokeExpr().getMethod().getName().equals("join") && node._obj.size() == 1) {

    		return allThreadNodes(node.threadName);

    	}
    	
    	Set<NodePEG> waitingNodes_kill = new HashSet<>();
    	
		if(stmt instanceof EnterMonitorStmt || node.nodeType.equals("notifiedentry")) {
    		if(node._obj.size()==1) {
    			
    		}
    	}
    
    	
    	if(node.nodeType.equals("notifyall")) {
    		
    		for(String s: node._obj) 
    		{
    			Set<NodePEG> nodes = _waitingNodesWithSameObj(s);
    			
    			for(NodePEG n:nodes)
    				waitingNodes_kill.add(n);
    			
    		}
    		return waitingNodes_kill;
    	}
    	
    	if(node.nodeType.equals("notify")) {
  
    		for(String s: node._obj) 
    		{
    			if(_waitingNodesWithSameObj(s).size() == 1)
    				waitingNodes_kill.addAll(_waitingNodesWithSameObj(s));
    		}
    		return waitingNodes_kill;
    	}
    	return waitingNodes_kill;
	}
	
	// returns the list of begin nodes corresponding to all objs of start node
    Set<NodePEG> getBeginNodesOfStart(NodePEG node) {

        Set<NodePEG> beginNodesOfStart = new HashSet<>();

        for(Edge succs: peg.get(node))
        {
        	if(succs.targetNode.nodeType.equals("Begin Node"))
        		beginNodesOfStart.add(succs.targetNode);
        }
            

        return beginNodesOfStart;
    }
    

	Set<NodePEG> GEN(NodePEG node)
	{
		//if n is start node, add begin nodes of all objects given by p2set
		Unit u = node.unit;
		Stmt s = (Stmt)u;
		
    	if(s.containsInvokeExpr() && s.getInvokeExpr().getMethod().getName().equals("start"))
    		return getBeginNodesOfStart(node);
    	
    	if(node.nodeType.equals("notifyAll") || node.nodeType.equals("notify")){
    		return getNotifySuccs(node);
    	}
    	if(s instanceof ExitMonitorStmt) 
    	{
    		for(NodePEG _n: allThreadNodes(node.threadName)) {
    			
    			if((Stmt)(_n.unit) instanceof EnterMonitorStmt) 
    			{
    				if(_hasIntersection(node._obj, _n._obj)) {
    					return findKillSETOfNode(_n);
    				}
    			}
    		}
    	}
    	return new HashSet<>();
	}
	
	Set<NodePEG> OUT(NodePEG node)
	{
		Set<NodePEG> res = setUnion(node.m, GEN(node));
		return setDiff(res, findKillSETOfNode(node));
	}
	
	void createREV_PEG() {
			
		Set<NodePEG> nodes = peg.keySet();
		
		for(NodePEG node:nodes)
		{
			rev_peg.put(node, new HashSet<>());
		}
		
		for(Map.Entry<NodePEG,Set<Edge>> entry: peg.entrySet()) {
			
			NodePEG node = entry.getKey();
			
			Set<Edge> succs = entry.getValue();
			
			for(Edge succ: succs) {
				
				Edge pred = new Edge(node, succ.edgeType);
				
				if(rev_peg.containsKey(succ.targetNode))
				{
					rev_peg.get(succ.targetNode).add(pred);
				}
				else
				{
					Set<Edge> preds = new HashSet<>();
					preds.add(pred);
					rev_peg.put(succ.targetNode, preds);
				}
				
			}
		}
	}

	
	void createPEG(SootMethod method, String currThread, NodePEG Caller)
	{
		
//		PointsToAnalysis pta = Scene.v().getPointsToAnalysis();
//    	
//		P2SetVisitor vis = new P2SetVisitor(){
//
//			@Override
//			public void visit(Node n) {
//				// TODO Auto-generated method stub
//				System.out.println("n: "+n.getType()+n.getNumber());
//			}
//    	};
		
		UnitGraph cfg = new BriefUnitGraph(method.getActiveBody());
		
		Set<String> thisVarP2set = new HashSet<>();
		
    	if(Caller.unit!=null) {
    		Stmt s = (Stmt) Caller.unit;
    		VirtualInvokeExpr vExp = (VirtualInvokeExpr)s.getInvokeExpr();
			Value base = vExp.getBase();
    		thisVarP2set = findPointsToList((Local)base);
    	}
		
		Map<Unit, NodePEG> unitNodeMap = new HashMap<>();
		
		// add cfg nodes in peg
		for(Unit unit:cfg)
		{
			NodePEG node = new NodePEG(new HashSet<>(thisVarP2set), unit, currThread, "");
			
			unitNodeMap.put(unit, node);
			
			peg.put(node, new HashSet<>());
						
		}
		
		// Add begin node and it's edges
		for(Unit unit:cfg.getHeads())
		{
			NodePEG BeginNode = new NodePEG(new HashSet<>(thisVarP2set), null, currThread, "Begin Node");
			Set<Edge> beginEdges = new HashSet<>();
			
			beginEdges.add(new Edge(unitNodeMap.get(unit), "Local"));
			
			peg.put(BeginNode, beginEdges);
			
			// Add Edge from caller node to current Node's begin Node
			if(!currThread.equals("_main"))
			{
				peg.get(Caller).add(new Edge(BeginNode, "Start Edge"));
				
			}
			allBeginNodes.add(BeginNode);
			break;
		}
		
		// Add normal CFG edges in PEG
		for(Unit unit : cfg) {
			
			NodePEG src = unitNodeMap.get(unit);
			List<Unit> succs = cfg.getSuccsOf(unit);
			
			String edgeType = "Local";
			
			for(Unit succ : succs) {
				
				NodePEG target = unitNodeMap.get(succ);
				
				Edge edge = new Edge(target, edgeType);
				
				peg.get(src).add(edge);
			}
		}
		
	// Add start node and it's run method in PEG
		
		for(Unit unit:cfg)
		{
			Stmt stmt = (Stmt) unit;
			VirtualInvokeExpr vExp = (VirtualInvokeExpr)stmt.getInvokeExpr();
			Value base = vExp.getBase();
			Type Class = base.getType();
			
			// if the node is start node
			if(stmt.containsInvokeExpr() && stmt.getInvokeExpr().getMethod().getName().equals("start"))
			{	
				Set<String> pointsToSet = findPointsToList((Local)base);
				
				NodePEG startNode = new NodePEG(pointsToSet, unit, currThread, "");
				
				unitNodeMap.put(unit, startNode);
				
				peg.put(startNode, new HashSet<>());
				
				for(SootMethod sm : _allMethods) {
    				
    				if(sm.getDeclaringClass().getName().equals(Class.toString())) {
    					
    					createPEG(sm, base.toString(), startNode);
    				}
    			}
			}
			// if the node is wait node
			else if(stmt.containsInvokeExpr() && stmt.getInvokeExpr().getMethod().getName().toString().equals("wait"))
			{	
				//PointsToSet ptSet = pta.reachingObjects((Local)base);
    			//PointsToSetInternal pti = (PointsToSetInternal)ptSet;
    			
    			//pti.forall(vis); //pti is the *PointsToSetInternal*
				
//				NodePEG waitNode = new NodePEG(base.toString(), unit, currThread, "");
//				
//				NodePEG waitingNode = new NodePEG(base.toString(), null, currThread, "Waiting");
//				
//				NodePEG notifiedEntry = new NodePEG(base.toString(), null, currThread, "Notified Entry");
//				
//				unitNodeMap.put(unit, waitNode);
//				
//				peg.put(waitNode, new HashSet<>());
//				peg.put(waitingNode, new HashSet<>());
//				peg.put(notifiedEntry, new HashSet<>());
//				
//				
//				
//				// for wait unit, we are putting notifiedEntry node mapping...... bcz in peg succs of wait node becomes 
//				// succs of notifiedEntry node
//				
//				peg.get(waitNode).add(new Edge(waitingNode, "Local"));
//				peg.get(waitingNode).add(new Edge(notifiedEntry, "Waiting"));
			}
			else if((stmt.containsInvokeExpr() && stmt.getInvokeExpr().getMethod().getName().toString().equals("join"))
					|| (stmt.containsInvokeExpr() && stmt.getInvokeExpr().getMethod().getName().toString().equals("notify"))
					|| (stmt.containsInvokeExpr() && stmt.getInvokeExpr().getMethod().getName().toString().equals("notifyAll")))
			{
				unitNodeMap.get(unit)._obj = findPointsToList((Local) base);
			}
			
			else if(stmt instanceof EnterMonitorStmt)
			{
				Value base_ = ((EnterMonitorStmt) stmt).getOp();
    			unitNodeMap.get(unit)._obj = findPointsToList((Local) base_);
			}
			else if(stmt instanceof ExitMonitorStmt)
			{
				Value base_ = ((ExitMonitorStmt) stmt).getOp();
    			unitNodeMap.get(unit)._obj = findPointsToList((Local) base_);
			}
			
		}
		
		// Add end node and it's corresponding edges
		for(Unit unit:cfg)
		{
			if(cfg.getSuccsOf(unit).isEmpty())
			{
				NodePEG endNode = new NodePEG(null, null, currThread, "End Node");
				HashSet<Edge> endEdges = new HashSet<>();
				
				endEdges.add(new Edge(endNode, "Local"));
				
				peg.put(unitNodeMap.get(unit), endEdges);
			}
		}
		
	}
	
	void getPEG() {
			
			for(Entry<NodePEG, Set<Edge>> entry : peg.entrySet()) {
				
				NodePEG src = entry.getKey();
				Set<Edge> edge = new HashSet<>(entry.getValue());
				
				for(Edge e : edge) {
					
					NodePEG target = e.targetNode;
					String eType = e.edgeType;
					
					//src.printNode();
					//System.out.println(eType);
					//target.printNode();
					//System.out.println();
					
				}
			}
	}
}