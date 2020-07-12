import java.util.Scanner;


/**
  * Euler objects are Graphs that are guaranteed to contain Euler Circuits
 because they are connected and all their vertices have even degree.
  * @author Sophie Quigley
  * @author PUT YOUR NAMES HERE
  * <BR>THE ONLY METHODS THAT SHOULD BE MODIFIED ARE:
  * <BR>FindEuler_H, newCircuit, 
  * and whichever helper function they need. 
  * 
  */
public final class Euler extends Graph{

/**
 * To specify backtracking algorithm to find Euler Circuit
 */    
    public static final int BACKTRACK=0;
/**
 * To specify Hierholzer (proof) algorithm to find Euler Circuit
 */    
    public static final int HIERHOLZER = 1;
    int count = 0;
    //int vertex = 0;
    /**
     * 
     * Creates a new undirected Graph containing an Euler Circuit.
     * This graph will be read from the Scanner in the input format of Graphs,
     * which are non-negative integers separated by white space as follows:
     * <ul>
     * <li>First positive integer specifies the number of vertices, n
     * <li>Next nxn integers specify the edges, listed in adjacency matrix order
     * </ul>
     * @param in Scanner used to read graph description
     * @throws InstantiationException when incorrect data is read or the graph does not contain an Euler circuit
     */
    Euler(Scanner in) throws InstantiationException {
        super(in);
        
        // Graph must be connected to have an Euler circuit
        if (!isConnected()) {
            throw new InstantiationException(
                "Graph has no Euler circuit because it is not connected.");
        }
        // To have an Euler circuit, all vertices must have even degree
        for (int i=0; i<totalV; i++) {
            // loops are counted twice in degree
            int degree = edges[i][i];
            for (int j=0; j<totalV; j++)
                degree += edges[i][j];
            if (degree %2 != 0 ) {
                throw new InstantiationException(
                        "Graph has no Euler circuit because vertex " + i + " had an odd degree.");             
            }
        }
    }       
    
    /**
     * Creates a randomly generated graph which contains an Euler circuit
     * because it is connected and all its vertices have even degree.
     * @throws InstantiationException if the parameters are invalid
     * @param vertices Number of vertices in graph - must be positive
     * @param maxParallelEdges Maximum number of parallel edges between any two vertices - must be non-negative
     */
    Euler( int vertices, int maxParallelEdges) throws InstantiationException {
        super(vertices, maxParallelEdges);
        int maxedges = maxParallelEdges+1;       
        do {
            // Get new set of edges until graph is connected
            while (!isConnected()) {
                populateEdges(maxParallelEdges);
                countEdges();
                countDegrees();
            }
            // Adjust adges to make sure that degrees of all vertices are even
            // And to remove loops which are irrelevant in Euler circuits
            for (int i=0; i<vertices-1; i++) {
                edges[i][i]=0;
                if (degreeV[i]%2 == 1) {
                    edges[i][vertices-1] = (edges[i][vertices-1]+1)% 2;
                    edges[vertices-1][i] = edges[i][vertices-1];
                    }
            }
            edges[vertices-1][vertices-1] = 0;
            // Note that adjusting edges may disconnect the graph 
            // because the % operation may return 0.
            // Therefore this process must be repeated until graph is connected.
        }   while (!isConnected());
        countEdges();
        countDegrees();
        clearVisited();
    }

    /**
     * Determine whether circuit parameter is a valid Euler circuit for graph.
     * @param circuit walk to be confirmed as Euler circuit
     * @return true iff circuit is a valid Euler circuit of the graph.
     */
    public boolean confirmEuler(Walk circuit) {
        int i, j, fromvertex, tovertex;
        if (!circuit.isCircuit())   return false;
        int circuitvertices = circuit.getTotalV();
        if (circuitvertices != totalE+1)    return false;
        clearVisited();
        fromvertex = circuit.getVertex(0);
        for (i=1; i<circuitvertices; i++) {
            tovertex = circuit.getVertex(i);
            unvisitedE[fromvertex][tovertex]--;
            if (fromvertex != tovertex) unvisitedE[tovertex][fromvertex]--;
            fromvertex = tovertex;
            }
        for (i=0; i<totalV; i++) 
            for (j=0; j<totalV; j++)
                if (unvisitedE[i][j] !=0)   return false;
        return true;
    }
    /**
     * Finds an Euler circuit in graph if there is one.
     * @param algorithm BACKTRACK or HIERHOLZER 
     * @return an Euler circuit for the graph if there is one, or null otherwise.
     */
    public Walk getEulerCircuit(int algorithm) {
        clearVisited();
        Walk euler = new Walk(totalE+1);
        switch (algorithm) {
        case BACKTRACK:
            euler.addVertex(0);
            FindEuler_B(0,0,totalE,euler);
            break;
        case HIERHOLZER:
            FindEuler_H(euler);            
            break;
        }    
        clearVisited();
        return euler;
    }
    /**
     * FindEuler_B implements a backtracking algorithm to find an Euler circuit
     * in a graph for which this has already been determined to be possible.
     * It is a recursive function that assumes that a trail has already been built 
     * from the starting vertex to the current vertex and attempts to complete an
     * Euler circuit back to the starting vertex using the remaining edges.
     * @param startV starting vertex in Euler circuit being built
     * @param currentV vertex at the end of trail built so far
     * @param remainingEs number of remaining edges
     * @param euler Walk being built - initialized with vertex 0 
     * @return True iff the Euler circuit has been successfully built 
     */
    private boolean FindEuler_B(int startV, int currentV, int remainingEs, Walk euler) {
        int nextV;
        
        if (remainingEs==0)
            return (currentV==startV);
        
        for (nextV=0; nextV<totalV; nextV++) {
            if (unvisitedE[currentV][nextV] != 0) {
                euler.addVertex(nextV);
                unvisitedE[currentV][nextV]--;
                if (currentV!=nextV)
                    unvisitedE[nextV][currentV]--;
                if (FindEuler_B(startV,nextV,remainingEs - 1,euler))
                    return true;
                euler.removeLastVertex();
                unvisitedE[currentV][nextV]++;
                if (currentV!=nextV)
                    unvisitedE[nextV][currentV]++;                
            }
        }
        
        // If this stage is reached, then there are no more edges from currentV
        // even though some edges are not in the circuit yet.
        return false;
    }
    
    /**
     * FindEuler_H implements Hierholzer's algorithm to find an Euler circuit
     * in a graph for which this has already been determined to be possible.
     * This is the algorithm covered in class and in the textbook
     * @param euler Walk being built - initially empty 
     */
    private void FindEuler_H(Walk euler) {
    	for(int i = 0; i<getTotalV(); i++)
    	{
    		
    		while(unvisitedDegreeV[i] != 0) {
    			count = 0;
    			Walk circuit = new Walk(100*(getTotalV()+1));
    		newCircuit(i, i, circuit);
    		euler.insertCircuit(circuit);
    		}
    		
    		//System.out.println("degree of " + i + " AFTER while loop = " + unvisitedDegreeV[i]);
    	}
    	
    }   
    
    /**
     * newCircuit creates a new circuit starting at vertex startV.
     * <br>Side effects:
     * <ul>
     * <li> edges added to circuit are removed from unvisitedE
     * <li> the unvisitedDegreeV of each affected vertex is decremented
 </ul>
     * @param startV first vertex in circuit
     * @param currentV vertex being currently added
     * @param circuit circuit being grown
     * @return number of edges added into the circuit (and traversed)
     */
    private int newCircuit(int startV, int currentV, Walk circuit) {
    	
    	//count1++;
    	int newCurrentV = 0;
    	circuit.addVertex(currentV);
    	for(int i = 0; i<getTotalV(); i++)
    	{
    		if(unvisitedE[currentV][i] != 0)
    		{
    			newCurrentV = i;
    			//System.out.println("Recursion no. " + count + " = "+newCurrentV);
    			break;
    		}
    	}
    	unvisitedDegreeV[currentV]--;
    	unvisitedE[currentV][newCurrentV]--;
    	if(currentV != newCurrentV) {
    		unvisitedE[newCurrentV][currentV]--;
    		unvisitedDegreeV[newCurrentV]--;
    	}
    	//System.out.println("currentV = " + unvisitedDegreeV[currentV] + "    newCurrentV = " + unvisitedDegreeV[newCurrentV]);
    	visitedE[currentV][newCurrentV]++;
    	if(currentV != newCurrentV)
    		visitedE[newCurrentV][currentV]++;
    	//System.out.println(unvisitedE[currentV][newCurrentV]);
    	if(startV == newCurrentV) {		
    		circuit.addVertex(newCurrentV);
    		//circuit.addVertex(0);
    		if(circuit.isCircuit() == true)
    		{
    			return count;
    		}
    		else if(circuit.isCircuit() == false)
    		{
    			//newCircuit(startV, newCurrentV, circuit);
    			//int vertex = circuit.getVertex(circuit.getTotalV()-1);
    			
    			//System.out.println("VERTEX = " + vertex);
    			//circuit.removeLastVertex();
    			circuit.addVertex(circuit.getVertex(0));
    			
    		}
    		/*System.out.println(circuit.isCircuit());
    		for(int i = 0; i<circuit.getTotalV()+1; i++)
    		{
    			System.out.println("vertex no. " + circuit.getVertex(i) + " from " + circuit.getTotalV());
    		}*/
    		return count;
    	}
    	else
    	
    		//System.out.println("startV = " + startV + "newCurrentV = " + newCurrentV);
    	return	newCircuit(startV, newCurrentV, circuit);
    }
    
}