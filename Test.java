import java.util.Scanner;

/**
 * Main test program offers the ability to test and profile
 * randomly generated graphs as well as graphs read from Scanner
 * @author Sophie Quigley
 * <br>Except for the two profiling functions, profile and profile1,
 * you can modify this testing program as you wish to perform your tests
 */
public class Test {
    /**
     * Test graph
     */
    private static Euler graph;
    /**
     * Input stream
     */
    private static Scanner in = new Scanner(System.in);
    /**
     * Main test program any combination of testRandom, testInput, or profile.
     * @param args the command line arguments
     */     
    public static void main(String[] args) {
        testRandom();
        //testInput();
        //profile();
    }
    
   /**
    * Loops, generating random graphs guaranteed to contain an Euler circuit,
    * and looking for such a circuit in each graph
    */ 
    private static void testRandom() {
        for (int max=1; max<=10; max++) {
            try {
                graph = new Euler(50,max);
                processGraph();
            }
            catch (InstantiationException e) {
                System.out.println(e);
            }
        }        
    }
    
    /**
    * Loops, reading graphs containing Euler circuits from scanner, 
    * and looking for such a circuit in each graph
    */ 
    private static void testInput() {
        while (in.hasNext())    {
            try {
                graph = new Euler(in);
                processGraph();
            }
            catch (InstantiationException e) {
                System.out.println(e);
            }
        }
    }
    
    /**
     * Prints graph, then profiles finding an Euler circuits for it using both algorithms.
     */
    private static void processGraph() {
        // Print graph
        System.out.println("Graph has " + graph.getTotalV() 
            + " vertices, and " + graph.getTotalE() + " edges.");
        System.out.print(graph);
        
        profile1(Euler.HIERHOLZER, "Hierholzer", true);       
        profile1(Euler.BACKTRACK, "backtracking", true);
    }
    
    /**
     * Finds an Euler circuit in graph using specified algorithm
     * and times how long it takes to do so.
     * @param algorithm Euler.BACKTRACK or Euler.HIERHOLZER
     * @param algorithmName name of algorithm
     * @param printmessages true to print messages
     * @return Time taken by the algorithm to find Euler circuit
     */
    private static long profile1(int algorithm, String algorithmName, Boolean printmessages) {
        long startTime = System.nanoTime();
        Walk circuit = graph.getEulerCircuit(algorithm);
        long estimatedTime = System.nanoTime() - startTime;        
        if (printmessages) {
            System.out.println( "Found Euler Circuit:\n" + circuit);        
            if (graph.confirmEuler(circuit))
                System.out.println("Valid Euler Circuit");
            else
                System.out.println("Invalid Euler Circuit");
            System.out.println("Time to construct by " + algorithmName +": " + estimatedTime);
        }
        return estimatedTime;        
    }
    
    /**
     * Number of iterations used to compute average cost of algorithms for each graph size
     */
    private static final int ITERATE = 20;
    /**
     * Profiles both algorithms on graphs of increasing size and complexity.
     * <br>
     * Outputs results in csv format including header line
     */
    private static void profile() {
        long Btime, Htime;
        int edges;
        System.out.println("Vertices,Max Edges,Edges,Hierholzer,Backtracking,H/B");
        try {
            for (int vertices=10; vertices<=200; vertices+=10) {
                for (int max=1; max<=3; max++) {
                    edges = 0;
                    Btime = 0;
                    Htime = 0;
                    for (int i =0; i<ITERATE; i++) {
                        graph = new Euler(vertices,max);
                        edges += graph.getTotalE();
                        Htime += profile1(Euler.HIERHOLZER, "Hierholzer", false);       
                        Btime += profile1(Euler.BACKTRACK, "backtracking", false);
                    }
                    edges = edges/ITERATE;
                    Btime = Btime/ITERATE;
                    Htime = Htime/ITERATE;
                    double ratio =  (double)Htime/(double)Btime;
                    int percent =  (int) Math.floor(ratio * 100);
                    System.out.println(vertices + "," +max+ "," + edges +","+ Htime +"," + Btime + "," + percent + "%");                    
                }
            }
        }
        catch (InstantiationException e) {
            System.out.println(e);
        }
    }
        
    
}
