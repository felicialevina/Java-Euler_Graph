/**
 * Walk objects can be used to build walks from Graphs.
 * A Walk is simply a list of vertices in the order in which they 
 occur in the walk.  The edges are not listed.
 * <br>Note that this class does not verify the validity of the walk,
 * i.e. it does not verity whether there are valid edges between two 
 * adjacent vertices in the walk.
 * @author Sophie Quigley
 * <BR>DO NOT MODIFY THIS CLASS
 *
 */
public class Walk {
    /**
     * Marker for no vertex
     */
    public static final int NOVERTEX = -1;
    /**
     * Maximum number of vertices in the walk.
     */
    int maxV;
    /**
     * Actual number of vertices in walk.
     */
    int totalV;
    /**
     * The vertices are listed in their order of traversal.
     * <br>Edges are not stored in this representation of walks.
     */
    int[] vertices;
   
    /**
     * Creates a new empty Walk with specified maximum number of vertices.
     * @param maxVertices maximum number of vertices in walk
     */
    Walk(int maxVertices) {
        maxV = maxVertices;
        vertices = new int[maxVertices];
        totalV = maxVertices;
        clear();
    }
    /**
     * Clears the walk of all vertices
     */
    public final void clear() {
        for (int i=0; i<totalV; i++)    
            vertices[i] = NOVERTEX;
        totalV = 0;        
    }
   /**
    * Returns a String representation of the walk
    * which is simply a list of vertices separated by blanks.
    * @return The list of vertices in the walk separated by blanks
    * 
    */
    @Override
    public String toString() {
        String result = "";
        for (int i=0; i<totalV; i++) {
            result += vertices[i];
            result += " ";
       }
       return result;
    }
    
    /**
     * Decides whether walk is empty
     * @return True iff the walk is empty
     */
    public boolean isEmpty() {
        return (totalV ==0);   
    } 
    
    /**
     * Decides whether walk is trivial
     * @return True iff the walk is trivial
     */
    public boolean isTrivial() {
        return (totalV ==1);   
    } 
    
    /**
     * Decides whether walk is a circuit
     * @return True iff the walk is a circuit
     */
    public boolean isCircuit() {
        if (totalV ==0)
            return false;
        return (vertices[0] == vertices[totalV-1]); 
    }

   /**
    * Returns the number of vertices in the walk.
    * <br>Note that in circuits the starting vertex will be counted twice.
    * @return The number of vertices in the walk
    *
    */  
    public int getTotalV() {
        return totalV;
    }
    
   /** 
    * Adds another vertex to the end of the walk if possible.
    * (i.e right before returning to the first vertex).
    * @param vertex Vertex to be added to walk
    * @return True iff the vertex could be added, i.e maxV was not reached
    * 
    */  
    public boolean addVertex(int vertex) {
        if (totalV == maxV)
            return false;
        vertices[totalV++] = vertex;
        return true;
    }
    
   /** 
    * Removes the last vertex added to walk if possible.
    * @return True iff the last vertex could be removed, i.e walk was not empty
    * 
    */  
    public boolean removeLastVertex() {
        if (totalV == 0)
            return false;
        vertices[--totalV] = NOVERTEX;
        return true;
    }
    
    /**
     * Returns the nth vertex in the walk or Walk.NOVERTEX if there is no nth vertex.
     * Counting starts at 0.
     * @param n The position of the vertex to be returned, starting at 0.
     * @return the vertex at position n in the walk
     * or Walk.NOVERTEX if the walk doesn't have n vertices.
     */
    public int getVertex(int n) {
        if (n == totalV)
            return vertices[0];
        if (n>=0 && n<totalV)
            return vertices[n];
        else
            return NOVERTEX;
        
    }
    
    /**
     * Insert a circuit to the walk.  The circuit is inserted in the walk 
     * replacing the <b>last</b> occurrence of its initial vertex in the walk.
     * When the walk is empty the circuit is added to it.
     * @param circuit circuit to be inserted into the walk
     * @return true iff insertion is successful
     */
    public boolean insertCircuit(Walk circuit) {
        int length, vertex, insertion, i;
        if (!circuit.isCircuit())   
            return false;
        // when walk is empty, initialize it with first vertex of circuit
        if (totalV == 0)
            this.addVertex(circuit.getVertex(0));
        // length of inserted circuit does not include first vertex already in walk
        length = circuit.getTotalV() - 1;
        if (totalV + length > maxV)    
            return false;
        // Locate insertion point
        vertex = circuit.getVertex(0);
        for (insertion=totalV; 
                insertion>=0 && vertices[insertion]!= vertex; insertion--);
        if (insertion == 0 & vertices[0]!=vertex)
            return false;
        // Shift vertices after insertion point to make room for circuit
        for (i=totalV-1; i>insertion; i--)
            vertices[i+length] = vertices[i];
        // Insert circuit at inserion point
        for (i=1; i<=length; i++)
            vertices[insertion+i] = circuit.getVertex(i);
        totalV += length;
        return true;
    }
}