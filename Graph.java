import java.util.Scanner;
import java.util.Random;

/**
  * Graph objects can be used to work with undirected graphs.
  * They are internally represented using adjacency matrices.
  * @author Sophie Quigley
  * <BR>DO NOT MODIFY THIS CLASS
  * 
  */
public class Graph {
    /**
     * Total number of vertices in graph
     */
    int totalV = 0;
    /**
     * Adjacency matrix of graph.
     * <br>edges[x][y] is the number of edges from vertex x to vertex y.
     */
    int[][] edges;
    /**
     * Total number of edges in graph
     */
    int totalE = 0;
    /**
     * Degree of each vertex.
     */
    int[] degreeV;
    /**
     * Used by graph visitors to keep track of visited vertices.
     */
    boolean[] visitedV;
    /**
     * Used by graph visitors to keep track of the degree of each vertex
     * if only unvisited edges are counted.
     */
    int[] unvisitedDegreeV;
    /**
     * Used by graph visitors to keep track of visited edges.
     */
    int[][] visitedE;
    /**
     * Used by graph visitors to keep track of unvisited edges
     * as an alternative to using visitedE.
     */
    int[][] unvisitedE;
    /**
     * Used to generate edges randomly
     */
    static Random rand = new Random(999);   
 
    /**
     * 
     * Creates a new undirected Graph whose content will be read from the Scanner.
     * <br>Input format consists of non-negative integers separated by white space as follows:
     * <ul>
     * <li>First positive integer specifies the number of vertices n
     * <li>Next nxn integers specify the edges, listed in adjacency matrix order
     * </ul>
     * @throws InstantiationException if incorrect data is read
     * @param in Scanner used to read graph description
     */
    Graph(Scanner in) throws InstantiationException {

        // Read number of totalV
        totalV = in.nextInt();
        if (totalV <= 0) {
            throw new InstantiationException("Number of vertices must be positive");
        }
        
        // If mistakes are found in rest of data, the entire matrix is read
        // before the exception is thrown,
        boolean inputMistake = false;
        InstantiationException e = null;
        int i, j;
        
        // Read adjacency matrix        
        edges = new int[totalV][totalV];
        for (i=0; i<totalV; i++) {
            for (j=0; j<totalV; j++) {
                edges[i][j]=in.nextInt();
                if (edges[i][j] <0){
                    e = new InstantiationException("Number of edges cannot be negative");
                    inputMistake = true;            
                }
            }
        }
        if (inputMistake) throw e; 
        
        // Verify that adjacency matrix is symmetric
        for (i=0; i<totalV; i++)
            for (j=i+1; j<totalV; j++)
                if (edges[i][j] != edges[j][i]) {
                    throw new InstantiationException("Adjacency matrix is not symmetric");
                }

        // Count edges in graph
        countEdges();

        // Count degrees of totalV
        degreeV = new int[totalV];
        countDegrees();      
        
        // Prepare visitation status arrays
        unvisitedDegreeV = new int[totalV];
        visitedV = new boolean[totalV];
        visitedE = new int[totalV][totalV];
        unvisitedE = new int[totalV][totalV];   
        clearVisited();
    }
    
    /**
     * Creates a randomly generated graph according to specifications.
     * @throws InstantiationException if the specifications are faulty
     * @param vertices Number of vertices in graph - must be non-negative
     * @param maxParallelEdges Maximum number of parallel edges between any two vertices - must be non-negative
     */
     Graph( int vertices, int maxParallelEdges )  throws InstantiationException {

        // Check validity of parameters
        if (vertices < 0) {
            throw new InstantiationException("Error: number of vertices cannot be negative");
        }
        if (maxParallelEdges <0) {
            throw new InstantiationException("Error: maxVertexDegree cannot be negative");
        }
        this.totalV = vertices;

        // Return empty graph
        if (vertices == 0) {
            return;
        }

        edges = new int[vertices][vertices];
        populateEdges(maxParallelEdges);
        countEdges();
        
        // Count degrees of totalV
        degreeV = new int[vertices];
        countDegrees();
               
        // Prepare visitation status arrays
        unvisitedDegreeV = new int[vertices];
        visitedV = new boolean[vertices];
        visitedE = new int[vertices][vertices];
        unvisitedE = new int[vertices][vertices];   
        clearVisited();
 }

     /**
     * Add random edges to a graph
     * @param maxParallelEdges Maximum number of parallel edges between any two vertices - must be non-negative
     */        
    final void populateEdges( int maxParallelEdges) {
        if (maxParallelEdges ==0)
            return;
        int randmax = maxParallelEdges+1;
        for (int i=0; i<totalV; i++)
            for (int j=i; j<totalV; j++) {
                edges[i][j] = rand.nextInt(randmax); 
                edges[j][i] = edges[i][j];
            }
    }

    /**
     * Set totalE to the total number of edges in the graph
     */           
    final void countEdges() {
        totalE = 0;
        for (int i=0; i<totalV; i++)
            for (int j=i; j<totalV; j++)
                totalE += edges[i][j];        
    }
    
    /**
     * Set degreeV array with degree of all vertices
     */
    final void countDegrees() {
        for (int i=0; i<totalV; i++) {
            degreeV[i] = 0;
            for (int j=0; j<totalV; j++)
                degreeV[i] += edges[i][j];
            //  loops count twice
            degreeV[i] += edges[i][i];    
        }
    }
    /**
     * Resets unvisitedDegreeV, visitedV, visitedE, and unvisitedE matrices for a new visitation
     */
    final void clearVisited() {
        for (int i=0; i<totalV; i++) {
            unvisitedDegreeV[i] = degreeV[i];
            visitedV[i] = false;
            for (int j=0; j<totalV; j++) {
                visitedE[i][j] = 0;
                unvisitedE[i][j] = edges[i][j];
            }
        }
    }
    
   /**
    * Returns a String representation of the graph
    * which is a 2-D representation of the adjacency matrix of that graph.
    * @return The 2-D representation of the adjacency matrix of that graph.
    * 
    */    
    @Override
    public final String toString() {
        return matrixtoString(edges);
    }

    /**
     * Returns a String representation of 2 dimensional matrix
 of size totalV x totalV.  
     * This can be used to visualize edges, visitedE, and unvisitedE
     * @param matrix matrix to be represented
     * @return 2D string representation of matrix
     */
    private String matrixtoString(int[][] matrix) {
        String result = "";
        for (int i=0; i<totalV; i++) {
            for (int j=0; j<totalV; j++) {
                result += matrix[i][j];
                result += " ";
            }
            result += "\n";
        }
        return result;
         
    }
    
    /**
    * Returns the number of vertices in the graph.
    * @return The number of vertices in the graph.
    *
    */  
    public final int getTotalV() {
        return totalV;
    }
    
    /**
    * Returns the number of edges in the graph.
    * @return The number of edges in the graph.
    *
    */  
    public final int getTotalE() {
        return totalE;
    }   
    
    /**
     * Returns the adjacency matrix of the graph
     * @return The adjacency matrix of the graph 
     */
    public final int[][] getAllEdges() {
        return edges;
    }
    
    /**
     * Returns the number of edges from sourceV to destV 
     * @param sourceV The source vertex
     * @param destV The destination vertex
     * @return the number of edges from sourceV to destV
     */
    public final int getEdges(int sourceV, int destV) {
        if (sourceV>=0 && sourceV<totalV && destV>=0 && destV<totalV)
            return edges[sourceV][destV];
        else
            return 0;
    }  

    /**
     * Verifies whether graph is empty (i.e. with 0 vertices)
     * @return True iff graph is empty
     */
    public final boolean isEmpty() {
        return (totalV == 0);        
    }
    
      
    /**
     * Verifies whether graph is connected
     * @return True iff graph is connected
     */
    public final boolean isConnected() {
        clearVisited();
        DFSvisit(0);
        for (int i=0; i<totalV; i++)  
            if (!visitedV[i]) {
                clearVisited();
                return false;
            }
        clearVisited();
        return true;        
    }
    
    /**
     * Conducts a Depth First Search visit of the unvisited vertices 
 of the graph starting at vertex.  
     * <br>Ties between vertices are broken in numeric order.
 <br>Used by isConnected()
     * @param vertex First vertex to be visited.
     */
    private void DFSvisit(int vertex) {
        visitedV[vertex] = true;
        for (int i=0; i<totalV; i++)
            if (edges[vertex][i]!=0 && !visitedV[i])
                DFSvisit(i);
    } 

    
}