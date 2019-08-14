package sat;

import org.sat4j.minisat.*;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.*;

import java.io.IOException;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.BufferedReader;
import java.io.FileReader;

import com.bpodgursky.jbool_expressions.Expression;
import com.bpodgursky.jbool_expressions.And;
import com.bpodgursky.jbool_expressions.Or;
import com.bpodgursky.jbool_expressions.Not;
import com.bpodgursky.jbool_expressions.Variable;
import com.bpodgursky.jbool_expressions.parsers.ExprParser;
import com.bpodgursky.jbool_expressions.rules.RuleSet;

import java.util.Scanner;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Sat {

     /* A farmer wants to cross a river and take with him a wolf, a goat, and a cabbage.

        There is a boat that can fit himself plus either the wolf, the goat, or the cabbage.

        If the wolf and the goat are alone on one shore, the wolf will eat the goat. If the goat and the cabbage are alone on the shore, the goat will eat the cabbage.

        How can the farmer bring the wolf, the goat, and the cabbage across the river?  */

    /* Solution
        Farmer takes Goat across (leaving Wolf and Cabbage behind)
        Farmer returns alone
        Farmer takes Wolf across
        Farmer returns with Goat

        * We now have the Farmer, the Cabbage and the Goat on one side and the Wolf on the other side

        Farmer takes Cabbage across
        Farmer returns alone
        Farmer takes Goat across

        DONE!  */

    public static ISolver solver;

    /*
        Taken an string as the input, this function returns a list of string representing the equivalent 
        cnf form of the input. Each element string in the list is a clause (disjunctions of literals), and
        the list represents the conjunction of such disjunctions.
    */
    private static List<String> string_2_cnf(String formula_str) {
        Expression<String> parsedExpression = RuleSet.toCNF(ExprParser.parse(formula_str));
        String parsed_exp_str = parsedExpression.toString();

        List<String> cnf = new ArrayList<String>();

        for (String clause: parsed_exp_str.split("&")){
            cnf.add(clause.trim().replace("(", "").replace(")", "").replace(" | ", " ").replace("!", "-"));
        }

        return cnf;
    }

    private static void gen_induction(List<String> variables, List<String> initial_state, List<String>  constraints, 
                                      List<String>  transitions, List<String>  final_state,
                                      int induction_step){ 
        try {
            int crossing_num = induction_step;


            // Try to generate the cnf
            List<String> cnf_list = new ArrayList<String>();


            if (induction_step < 2) {
                // cnf for initial state
                for (String each_initial_state: initial_state){
                    for (int var_idx=0; var_idx<variables.size(); var_idx++) {
                        String variable = variables.get(var_idx);
                        each_initial_state = each_initial_state.replace(variable + "_0", String.valueOf(var_idx+1));
                    }
                    cnf_list.addAll(string_2_cnf(each_initial_state));
                }
            }


            // cnf for constraints over states k-1, k, and k+1
            for (int crossing_idx=0; crossing_idx<=crossing_num; crossing_idx++) {
                for (String constraint: constraints){                
                    String crossing_idx_constraint = constraint;
                    for (int var_idx=0; var_idx<variables.size(); var_idx++){
                        String variable = variables.get(var_idx);
                        crossing_idx_constraint = crossing_idx_constraint.replace(variable, 
                                        String.valueOf(var_idx+variables.size()*crossing_idx+1));
                    }
                    cnf_list.addAll(string_2_cnf(crossing_idx_constraint));
                }
            }

            // cnf for transitions
            for (int crossing_idx=0; crossing_idx<crossing_num; crossing_idx++) {
                for (String transition: transitions) {

                    // If k-1 is in the constraint and crossing_idx is 0, we should ignore such a constraint
                    if (crossing_idx == 0 && transition.contains("{k-1}")) {
                        continue;
                    }

                    String crossing_idx_transition = transition;
                    for (int var_idx=0; var_idx<variables.size(); var_idx++){
                        String variable = variables.get(var_idx);
                        crossing_idx_transition = crossing_idx_transition.replace(variable+"_{k-1}", 
                                        String.valueOf(var_idx+variables.size()*(crossing_idx-1)+1));
                        crossing_idx_transition = crossing_idx_transition.replace(variable+"_k", 
                                        String.valueOf(var_idx+variables.size()*crossing_idx+1));
                        crossing_idx_transition = crossing_idx_transition.replace(variable+"_{k+1}", 
                                        String.valueOf(var_idx+variables.size()*(crossing_idx+1)+1));
                    }
                    cnf_list.addAll(string_2_cnf(crossing_idx_transition));
                }
            }
            // cnf for final state
            for (int crossing_idx=0; crossing_idx<=crossing_num; crossing_idx++) {
                for (String each_final_state: final_state){
                    for (int var_idx=0; var_idx<variables.size(); var_idx++) {
                        String variable = variables.get(var_idx);
                        each_final_state = each_final_state.replace(variable + "_n", 
                                        String.valueOf(var_idx + crossing_num*variables.size() + 1));

                        each_final_state = each_final_state.replace(variable + "_{n-1}", 
                                        String.valueOf(var_idx + (crossing_num-1)*variables.size() + 1));
                    }

                    if (crossing_idx == crossing_num) {
                        cnf_list.addAll(string_2_cnf(each_final_state));
                    } else {
                        cnf_list.addAll(string_2_cnf("!(" + each_final_state + ")"));
                    }
                }
            }

            // System.out.println(cnf_list);
            // System.out.println(cnf_list.size());
            // System.out.println(4*2+18*crossing_num);

            BufferedWriter writer = new BufferedWriter(new FileWriter("src/main/resources/generated.cnf"));
            writer.write(String.format("p cnf %d %d\n", 
                                        (crossing_num+1)*variables.size(), 
                                        cnf_list.size()));
                                        // 4*2+18*crossing_num));
                                        // 4*(crossing_num+2)+2*crossing_num));
            
            for (String clause: cnf_list) {
                writer.write(clause+" 0\n");
            }

            writer.close();
        }  catch (IOException e) {
            System.out.println("Exception");
        }
    }

    /*
        type: 0 for checking invariants, 1 for finding solution when invariants does not satisfy, 
              2 for checking final state
    */
    private static void gen_problem(int crossing_num, List<String> variables, List<String> initial_state,
                                    List<String> constraints, List<String> transitions, 
                                    List<String> invariants, List<String> final_state, int type){
        try {

            // Try to generate the cnf
            List<String> cnf_list = new ArrayList<String>();


            // cnf for initial state
            for (String each_initial_state: initial_state){
                for (int var_idx=0; var_idx<variables.size(); var_idx++) {
                    String variable = variables.get(var_idx);
                    each_initial_state = each_initial_state.replace(variable + "_0", String.valueOf(var_idx+1));
                }
                cnf_list.addAll(string_2_cnf(each_initial_state));
            }

            // cnf for constraints over states
            for (int crossing_idx=0; crossing_idx<=crossing_num; crossing_idx++) {
                for (String constraint: constraints){                
                    String crossing_idx_constraint = constraint;
                    for (int var_idx=0; var_idx<variables.size(); var_idx++){
                        String variable = variables.get(var_idx);
                        crossing_idx_constraint = crossing_idx_constraint.replace(variable, 
                                        String.valueOf(var_idx+variables.size()*crossing_idx+1));
                    }
                    cnf_list.addAll(string_2_cnf(crossing_idx_constraint));
                }
            }

            // cnf for transitions
            for (int crossing_idx=0; crossing_idx<crossing_num; crossing_idx++) {
                for (String transition: transitions) {

                    // If k-1 is in the constraint and crossing_idx is 0, we should ignore such a constraint
                    if (crossing_idx == 0 && transition.contains("{k-1}")) {
                        continue;
                    }

                    String crossing_idx_transition = transition;
                    for (int var_idx=0; var_idx<variables.size(); var_idx++){
                        String variable = variables.get(var_idx);
                        crossing_idx_transition = crossing_idx_transition.replace(variable+"_{k-1}", 
                                        String.valueOf(var_idx+variables.size()*(crossing_idx-1)+1));
                        crossing_idx_transition = crossing_idx_transition.replace(variable+"_k", 
                                        String.valueOf(var_idx+variables.size()*crossing_idx+1));
                        crossing_idx_transition = crossing_idx_transition.replace(variable+"_{k+1}", 
                                        String.valueOf(var_idx+variables.size()*(crossing_idx+1)+1));
                    }
                    cnf_list.addAll(string_2_cnf(crossing_idx_transition));
                }
            }

            if (type == 0){
                // cnf for checking invariants
                for (int crossing_idx=0; crossing_idx<=crossing_num; crossing_idx++) {
                    for (String invariant: invariants){                
                        String crossing_idx_invariant = invariant;
                        for (int var_idx=0; var_idx<variables.size(); var_idx++){
                            String variable = variables.get(var_idx);
                            crossing_idx_invariant = crossing_idx_invariant.replace(variable, 
                                            String.valueOf(var_idx+variables.size()*crossing_idx+1));
                        }
                        cnf_list.addAll(string_2_cnf(crossing_idx_invariant));
                    }
                }
            } else if (type == 1){
                // cnf for checking invariants
                for (int crossing_idx=0; crossing_idx<crossing_num; crossing_idx++) {
                    for (String invariant: invariants){                
                        String crossing_idx_invariant = invariant;
                        for (int var_idx=0; var_idx<variables.size(); var_idx++){
                            String variable = variables.get(var_idx);
                            crossing_idx_invariant = crossing_idx_invariant.replace(variable, 
                                            String.valueOf(var_idx+variables.size()*crossing_idx+1));
                        }
                        cnf_list.addAll(string_2_cnf(crossing_idx_invariant));
                    }
                }

                if (invariants.size() > 0) {
                    String final_invariant = String.join(" & ", invariants);
                    final_invariant = "!(" + final_invariant + ")";
                    
                    for (int var_idx=0; var_idx<variables.size(); var_idx++){
                        String variable = variables.get(var_idx);
                        final_invariant = final_invariant.replace(variable, 
                                        String.valueOf(var_idx+variables.size()*crossing_num+1));
                    }
                    cnf_list.addAll(string_2_cnf(final_invariant));
                }
                
            } else if (type == 2) {
                // cnf for final state
                for (String each_final_state: final_state){
                    for (int var_idx=0; var_idx<variables.size(); var_idx++) {
                        String variable = variables.get(var_idx);
                        each_final_state = each_final_state.replace(variable + "_n", 
                                        String.valueOf(var_idx + crossing_num*variables.size() + 1));

                        each_final_state = each_final_state.replace(variable + "_{n-1}", 
                                        String.valueOf(var_idx + (crossing_num-1)*variables.size() + 1));
                    }
                    cnf_list.addAll(string_2_cnf(each_final_state));
                }
            }

            // System.out.println(cnf_list);
            // System.out.println(cnf_list.size());
            // System.out.println(4*2+18*crossing_num);

            BufferedWriter writer = new BufferedWriter(new FileWriter("src/main/resources/generated.cnf"));
            writer.write(String.format("p cnf %d %d\n", 
                                        (crossing_num+1)*variables.size(), 
                                        cnf_list.size()));
                                        // 4*2+18*crossing_num));
                                        // 4*(crossing_num+2)+2*crossing_num));
            
            for (String clause: cnf_list) {
                writer.write(clause+" 0\n");
            }

            // // variable for tracking minisat variable
            // int current_variable = 0;

            // // 1 for farmer, 2 for wofl, 3 for goat, 4 for cabbage. 
            // // Initially all four objects are on the left bank
            // int init_f = current_variable + 1;
            // int init_w = current_variable + 2;
            // int init_g = current_variable + 3;
            // int init_c = current_variable + 4;
            // writer.write(String.format("%d 0\n", init_f));
            // writer.write(String.format("%d 0\n", init_w));
            // writer.write(String.format("%d 0\n", init_g));
            // writer.write(String.format("%d 0\n", init_c));
            // current_variable = current_variable + 4;
            

            // // iteration crossing_num:
            // for(int i=1; i<=crossing_num; i++){  
            //     int inter_f = current_variable + 1;
            //     int inter_w = current_variable + 2;
            //     int inter_g = current_variable + 3;
            //     int inter_c = current_variable + 4;

            //     // Not danger at this step:
            //     writer.write(String.format("-%d -%d %d 0\n", inter_w, inter_g, inter_f));
            //     writer.write(String.format("%d %d -%d 0\n", inter_w, inter_g, inter_f));
            //     writer.write(String.format("-%d -%d %d 0\n", inter_g, inter_c, inter_f));
            //     writer.write(String.format("%d %d -%d 0\n", inter_g, inter_c, inter_f));

            //     // the farmer should be crossing
            //     writer.write(String.format("-%d -%d 0\n", inter_f, inter_f - 4));
            //     writer.write(String.format("%d %d 0\n", inter_f, inter_f - 4));

            //     // At most one animal can travel with the farmer
            //     writer.write(String.format("-%d %d -%d %d 0\n", inter_w, inter_w - 4,
            //                                 inter_g, inter_g - 4));
            //     writer.write(String.format("-%d %d %d -%d 0\n", inter_w, inter_w - 4,
            //                                 inter_g, inter_g - 4));
                
            //     writer.write(String.format("%d -%d %d -%d 0\n", inter_w, inter_w - 4,
            //                                 inter_g, inter_g - 4));
            //     writer.write(String.format("%d -%d -%d %d 0\n", inter_w, inter_w - 4,
            //                                 inter_g, inter_g - 4));

            //     writer.write(String.format("-%d %d -%d %d 0\n", inter_w, inter_w - 4,
            //                                 inter_c, inter_c - 4));
            //     writer.write(String.format("-%d %d %d -%d 0\n", inter_w, inter_w - 4,
            //                                 inter_c, inter_c - 4));

            //     writer.write(String.format("%d -%d %d -%d 0\n", inter_w, inter_w - 4,
            //                                 inter_c, inter_c - 4));
            //     writer.write(String.format("%d -%d -%d %d 0\n", inter_w, inter_w - 4,
            //                                 inter_c, inter_c - 4));

            //     writer.write(String.format("-%d %d -%d %d 0\n", inter_c, inter_c - 4,
            //                                 inter_g, inter_g - 4));
            //     writer.write(String.format("-%d %d %d -%d 0\n", inter_c, inter_c - 4,
            //                                 inter_g, inter_g - 4));
                
            //     writer.write(String.format("%d -%d %d -%d 0\n", inter_c, inter_c - 4,
            //                                 inter_g, inter_g - 4));
            //     writer.write(String.format("%d -%d -%d %d 0\n", inter_c, inter_c - 4,
            //                                 inter_g, inter_g - 4));

            //     current_variable = current_variable + 4;
            // }

            // // Finally, all 4 objects are on the right bank
            // int final_f = current_variable - 3;
            // int final_w = current_variable - 2;
            // int final_g = current_variable - 1;
            // int final_c = current_variable;
            // writer.write(String.format("-%d 0\n", final_f)); // 
            // writer.write(String.format("-%d 0\n", final_w)); // 
            // writer.write(String.format("-%d 0\n", final_g)); // 
            // writer.write(String.format("-%d 0\n", final_c)); // 

            writer.close();
        }  catch (IOException e) {
            System.out.println("Exception");
        }
    }

    private static String get_object_name(int sat_var) {
        switch(sat_var%4){
            case 1: case -1: 
                return "F";
            case 2: case -2:
                return "W";
            case 3: case -3:
                return "G";
            default:
                return "C";
        }
    }

    enum InputType {
          VARIABLES,
          INIT_STATE,
          CONSTRAINTS,
          TRANSITIONS,
          FINAL_STATE,
          INVARIANTS,
          NONE
        }

    private static void read_bool_exps(String input_file, List<String> variables, List<String> initial_state, 
                                       List<String> constraints, List<String> transitions, 
                                       List<String> invariants, List<String> final_state){
        BufferedReader reader;

        InputType input_type = InputType.NONE;
        try {
            reader = new BufferedReader(new FileReader(
                    input_file));
            String line = reader.readLine();
            while (line != null) {
                line = line.trim();
                // System.out.println(line);
                if (line.contains("Variables:")){
                    input_type = InputType.VARIABLES;
                    // System.out.println(line);
                } else if (line.contains("Initial state:")) {
                    // System.out.println(line);
                    input_type = InputType.INIT_STATE;
                } else if (line.contains("Constraints:")) {
                    // System.out.println(line);
                    input_type = InputType.CONSTRAINTS;
                } else if (line.contains("Transitions:")) {
                    // System.out.println(line);
                    input_type = InputType.TRANSITIONS;
                } else if (line.contains("Final state:")) {
                    // System.out.println(line);
                    input_type = InputType.FINAL_STATE;
                } else if (line.contains("Invariants:")) {
                    // System.out.println(line);
                    input_type = InputType.INVARIANTS;
                }else if (line.startsWith("//")) {
                    // Ingore the comments
                    // System.out.println(line); 
                } else if (!line.isEmpty()) {
                    // System.out.println(line);

                    switch (input_type) {
                        case VARIABLES:
                            // System.out.println(line);    
                            variables.addAll(Arrays.asList(line.split("\\s*,\\s*")));
                            break;
                        case INIT_STATE:
                            // System.out.println(line);
                            initial_state.add(line);
                            break;
                        case CONSTRAINTS:
                            constraints.add(line);
                            break;
                        case TRANSITIONS:
                            transitions.add(line);
                            break;
                        case INVARIANTS:
                            invariants.add(line);
                            break;
                        case FINAL_STATE:
                            final_state.add(line);
                            break;
                    }
                }
                // read next line
                line = reader.readLine();
            }
            reader.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public static void print_solution(IProblem problem, List<String> variables, Reader reader){
        int[] model = problem.model();
        // System.out.println(reader.decode(model));
        // String left = "";
        String step_state = "";
        for (int solution: model){
            int variable_idx = (Math.abs(solution)-1) % variables.size();
            // System.out.println(variable_idx);
            step_state = step_state + " " + variables.get(variable_idx);
            if (solution > 0){
                step_state = step_state + ":True";
            } else {
                step_state = step_state + ":False";
            }

            if (solution % variables.size() == 0){
                System.out.println(String.format("Step %d:", (Math.abs(solution) - 1) / variables.size()) + step_state);
                step_state = "";
            }
        }
    }

    public static boolean check_sat(Reader reader ){
        try {
            IProblem problem = reader.parseInstance("src/main/resources/generated.cnf");
            // IProblem  problem = reader.parseInstance("src/main/resources/simple_v3_c2.cnf");
            if (problem.isSatisfiable ()) {
                return true;
            }
        } catch (IOException e) {
            // System.out.println (e);
        } catch (ParseFormatException e) {
            // System.out.println (e);
        }  catch (ContradictionException e) {
            // System.out.println (e);
            // return false
            // System.out.println(String.format("We cannot reach the final state after %d steps", crossing_num));
            // if (crossing_num == max_crossing_num){
            //     System.out.println(String.format("No"));
            // }
        } catch (TimeoutException e) {
            // System.out.println (e);
        }

        return false;
    }

    public static void main(String[] args) {
        // Expression<String> expr = And.of(
        //     Variable.of("A"),
        //     Variable.of("B"),
        //     Or.of(Variable.of("C"), Not.of(Variable.of("C"))));
        // System.out.println(expr);

        // Expression<String> parsedExpression = RuleSet.toCNF(ExprParser.parse("( ( (! 0) | 1) & 2 & 3)"));
        // System.out.println(parsedExpression);

        // Store a list of variables
        ArrayList<String> variables = new ArrayList<String>();
        ArrayList<String> initial_state = new ArrayList<String>();
        ArrayList<String> constraints = new ArrayList<String>();
        ArrayList<String> transitions = new ArrayList<String>();
        ArrayList<String> invariants = new ArrayList<String>();
        ArrayList<String> final_state = new ArrayList<String>();

        read_bool_exps("input.txt", variables, initial_state, constraints, transitions, invariants, final_state);

        // System.out.println(variables);
        // System.out.println(initial_state);
        // System.out.println(constraints);
        // System.out.println(transitions);
        // System.out.println(invariants);
        // System.out.println(final_state);

        // Scanner input_reader = new Scanner(System.in);  // Reading from System.in
        // System.out.println("Enter the number of step: ");

        // int max_crossing_num;
        // while (true) {
        //     try {
        //         max_crossing_num = input_reader.nextInt(); // Scans the next token of the input as an int.
        //         break;
        //     } catch (Exception e) {
        //         // System.out.println(e);
        //         System.out.println("Please enter a valid number of step: ");                
        //         input_reader.next();
        //     }
        // }
        // // //once finished
        // input_reader.close();

        // Check by induction:
        // First, the final states does not hold at the first step
        solver = SolverFactory.newDefault();
        solver.setTimeout(3600);
        Reader reader = new DimacsReader(solver);

        for (int induction_step=0; induction_step<= 1; induction_step++) {
            gen_induction(variables, initial_state, constraints, transitions, final_state, induction_step);
            try {
                IProblem problem = reader.parseInstance("src/main/resources/generated.cnf");
                // IProblem  problem = reader.parseInstance("src/main/resources/simple_v3_c2.cnf");
                if (problem.isSatisfiable ()) {

                    System.out.println(String.format(String.format("Yes, collision in %d steps", induction_step)));

                    // System.out.println(String.format("CNF is satisfiable with %d crossings\nSolution:", crossing_num));
                    // reader.setVerbosity(true);
                    print_solution(problem, variables, reader);

                    return;
                }

            }  catch (IOException e) {
                // System.out.println (e);
            } catch (ParseFormatException e) {
                // System.out.println (e);
            }  catch (ContradictionException e) {
                // System.out.println (e);
                // System.out.println(String.format("We cannot reach the final state after %d steps", crossing_num));
                // if (crossing_num == max_crossing_num){
                //     System.out.println(String.format("No"));
                // }
            } catch (TimeoutException e) {
                // System.out.println (e);
            }
        }

        // Suppose at k-step, the final state constraint is not satisfied, then next step k+1, the final state
        // constraint is also not satisfied
        gen_induction(variables, initial_state, constraints, transitions, final_state, 2);
        try {
            IProblem problem = reader.parseInstance("src/main/resources/generated.cnf");
            // IProblem  problem = reader.parseInstance("src/main/resources/simple_v3_c2.cnf");
            if (problem.isSatisfiable ()) {
                
            } else {
                System.out.println("No, no collision by induction");
                return;
            }

        }  catch (IOException e) {
            // System.out.println (e);
        } catch (ParseFormatException e) {
            // System.out.println (e);
        }  catch (ContradictionException e) {
            // System.out.println (e);
            // System.out.println(String.format("We cannot reach the final state after %d steps", crossing_num));
            // if (crossing_num == max_crossing_num){
            //     System.out.println(String.format("No"));
            // }
            System.out.println("No, no collision by induction");
            return;
        } catch (TimeoutException e) {
            // System.out.println (e);
        }


        // int crossing_num = 1;
        // for (int crossing_num = 1; crossing_num <= max_crossing_num; crossing_num++) {
        for (int crossing_num = 0; ; crossing_num++) {
            // System.out.println(crossing_num);
            reader = new DimacsReader(solver);

            if (crossing_num == 0) {
                continue;
            }

            // System.out.println(crossing_num);

            gen_problem(crossing_num, variables, initial_state, constraints, transitions, invariants, final_state, 2);
            try {
                IProblem problem = reader.parseInstance("src/main/resources/generated.cnf");
                // IProblem  problem = reader.parseInstance("src/main/resources/simple_v3_c2.cnf");
                if (problem.isSatisfiable ()) {
                    System.out.println(String.format(String.format("Yes, collision in %d steps", crossing_num)));
                    // System.out.println(String.format("CNF is satisfiable with %d crossings\nSolution:", crossing_num));
                    // reader.setVerbosity(true);
                    print_solution(problem, variables, reader);

                    break;
                }  else {
                    // System.out.println(String.format("We cannot reach the final state after %d steps", crossing_num));
                    // if (crossing_num == max_crossing_num){
                    //     System.out.println(String.format("No"));
                    // }
                }

            }  catch (IOException e) {
                // System.out.println (e);
            } catch (ParseFormatException e) {
                // System.out.println (e);
            }  catch (ContradictionException e) {
                // System.out.println (e);
                // System.out.println(String.format("We cannot reach the final state after %d steps", crossing_num));
                // if (crossing_num == max_crossing_num){
                //     System.out.println(String.format("No"));
                // }
            } catch (TimeoutException e) {
                // System.out.println (e);
            }


        }
    }
}
