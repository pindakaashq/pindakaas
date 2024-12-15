package savilerow;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Saad Attieh
    
    This file is part of Savile Row.
    
    Savile Row is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    
    Savile Row is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
    
    You should have received a copy of the GNU General Public License
    along with Savile Row.  If not, see <http://www.gnu.org/licenses/>.

*/

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import savilerow.expression.*;
import savilerow.model.*;
import savilerow.solver.*;

public class SymmetryBreaker {

    public boolean detectAndBreakSymmetries(Model m) {
        try {
            String file = writeModelAsJSON(m);
            CmdFlags.println("Created output file " + file);
            ArrayList<Permutation> symmetries = getSymmetries(file);
            addConstraints(m, symmetries);
            return true;
        } catch (IOException e) {
            System.err.println("Error in symmetry breaker.");
            e.printStackTrace();
            return false;
        } catch (InterruptedException e) {
            System.err.println("Error in symmetry breaker.");
            e.printStackTrace();
            return false;
        }
    }

    // writes symbol table and constraints in model as json using their toJSON
    // methods
    public String writeModelAsJSON(Model m) throws IOException {
        // build json text
        StringBuilder bf = new StringBuilder();
        bf.append("{\n\"symmetricChildren\":true,\n"); // open JSON object and
                                                       // declare the following
                                                       // domains array to be
                                                       // symmetric

        // first - nodes that allowed to be swapped
        bf.append("\"nodes_to_swap\":");
        m.global_symbols.writeVarListAsJSON(bf);
        bf.append(",\n");

        // nextSymbolTable variable/domain mapping
        bf.append("\"variableDomains\":");
        m.global_symbols.writeVarDomainsAsJSON(bf);
        bf.append(",\n");

        // thenconstraints as tree
        bf.append("\"constraints\": ");
        m.constraints.toJSON(bf);
        if (m.objective != null) {
            bf.append(",\n");
            bf.append("\"objective\":");
            m.objective.toJSON(bf);
        }
        bf.append("\n}");

        // write to file

        // make file in same place as minion output
        String location = CmdFlags.minionfile;
        if (location.endsWith(".minion")) {
            location = location.substring(0, location.lastIndexOf(".minion"));
        }
        File f = new File(location + ".json");
        f.createNewFile();

        PrintWriter writer = new PrintWriter(f);
        writer.println(bf.toString());
        writer.close();
        return f.getPath();
    }

    // adds constraints to break the symmetries detected
    private void addConstraints(Model m, ArrayList<Permutation> permutations) {
        Permutation.setOrdering(buildBranchOrderingList(m));

        // make lex constraints
        // children of the And node made later
        ArrayList<ASTNode> constraints = new ArrayList<ASTNode>();
        m.constraints.getChild(0).setParent(null);  // Do not copy constraint set.
        constraints.add(m.constraints.getChild(0)); // previous top of
                                                    // constraint tree

        // add lex constraints
        for (Permutation p : permutations) {
            ASTNode l = CompoundMatrix.make(toIdentifierList(
                    Permutation.getOrdering(), m));

            ASTNode r = CompoundMatrix.make(toIdentifierList(
                    p.permutate(), m));

            constraints.add(new LexLessEqual(l, r));
        }
        And and = new And(constraints);
        m.constraints.setChild(0, and);
    }

    // copies list of string (variable manes) into list of Identifier objects
    private ArrayList<ASTNode> toIdentifierList(ArrayList<String> vars, Model m) {
        ArrayList<ASTNode> idents = new ArrayList<ASTNode>();
        for (String var : vars) {
            idents.add(new Identifier(m, var));
        }
        return idents;
    }

    public Collection<String> buildBranchOrderingList(Model m) {
        LinkedHashSet<String> branchingOrder = new LinkedHashSet<String>();
        for (int i = 1; i < m.branchingon.numChildren(); i++) {
            branchingOrder.add(((Identifier) m.branchingon.getChild(i))
                    .getName());
        }
        branchingOrder.addAll(m.global_symbols.getVarNamesList());
        return branchingOrder;
    }

    // runs external process to break symmetries and parses output
    private ArrayList<Permutation> getSymmetries(String fileName)
            throws IOException, InterruptedException {
        ArrayList<String> output = new ArrayList<String>();
        ReadProcessOutput p = new ReadProcessOutput(output);
        ArrayList<String> input = new ArrayList<String>();
        input.add(CmdFlags.getSymDetect());
        input.add("--json");
        input.add(fileName);
        RunCommand.runCommand(true, input, new ArrayList<String>(), p);
        return parseSymmetries(buildString(output));
    }

    private ArrayList<Permutation> parseSymmetries(String json) {
        ArrayList<Permutation> permutations = new ArrayList<Permutation>();
        Pattern jsonObjectPattern = Pattern.compile("\\{([^}]*)");
        Matcher m = jsonObjectPattern.matcher(json);
        while (m.find()) {
            String keyValues = m.group(1).trim();
            Permutation p = makePermutation(keyValues);
            permutations.add(p);
        }
        return permutations;
    }

    private Permutation makePermutation(String jsonObject) {
        try {
            Permutation p = new Permutation();
            String[] members = jsonObject.split(",\\s*");
            for (String member : members) {
                String[] kv = member.split(":");
                String key = kv[0].replaceAll("\"", "");
                String value = kv[1].replaceAll("\"", "");
                p.addMapping(SymbolTable.unescapeVar(key),
                        SymbolTable.unescapeVar(value));
            }
            return p;
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new IllegalStateException("Error in json syntax\n"
                    + jsonObject);
        }
    }

    // converts arraylist of strings into stringbuffer assuming each element is
    // a new line. i.e. line breaks are added between each element.
    private String buildString(ArrayList<String> lines) {
        StringBuilder bf = new StringBuilder();
        for (String line : lines) {
            bf.append(line + "\n");
        }
        return bf.toString();
    }

}
