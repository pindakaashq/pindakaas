package savilerow.eprimeparser;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Peter Nightingale
    
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;

import savilerow.CmdFlags;
import savilerow.expression.*;
import savilerow.model.*;

// EPrimeReader.java

public final class EPrimeReader {
    private EPrimeTokenizer tokens;

    private static final boolean VB_MTDS = false;

    static String[] ops = {"+", "-", "/", "*", "**", "%", "\\/", "/\\", "=>", "->", "<=>", "<->", "=", "!=", "<=", "<", ">=", ">", "<lex", "<=lex", ">lex", ">=lex", "union", "intersect", "subset", "subsetEq", "supset", "supsetEq", "in", "xor"};
    static String[] keywds = { "forall", "forAll", "exists", "sum", "such", "that", "letting", "given", "where", "find", "language", "int", "bool", "union", "intersect", "in", "false", "true" };
    
    private Model m;    // Only to be used when constructing Identifiers/Matrix Slice at the moment.
    
    private ASTNode branchingon;
    private ASTNode preservevariables;
    private String heuristic;
    
    // SNS related things
    private ArrayList<ASTNode> neighbourhoods;
    private ArrayList<ASTNode> groups;
    private ASTNode incumbentmapping;
    
    private HashSet<String> binops;    // set of binary operator strings created in ctor.

    private HashSet<String> keywords;
    
    private HashMap<String, FunctionDescription> funcs;
    
    /* ====================================================================
     constructor
    ==================================================================== */
    public EPrimeReader(String fn, boolean readFromFile) {
        tokens = new EPrimeTokenizer(fn, readFromFile);
        
        binops = new HashSet<String>(Arrays.asList(ops));
        m = new Model();   // Empty model created here.
        
        keywords = new HashSet<String>(Arrays.asList(keywds));
        populateGenericFunctions();
        
        neighbourhoods = new ArrayList<ASTNode>();
        groups=new ArrayList<ASTNode>();
    }
    
    private void populateGenericFunctions() {
        funcs=new HashMap<String, FunctionDescription>();
        funcs.put("toSet", new FunctionDescription("ToSet", 1));
        funcs.put("popcount", new FunctionDescription("Popcount", 1));
        funcs.put("toInt", new FunctionDescription("ToInt", 1));
        funcs.put("count", new FunctionDescription("Count", 2));
        funcs.put("makeTable", new FunctionDescription("MakeTable", 1));
        funcs.put("indexOf", new FunctionDescription("IndexOf", 1));
        funcs.put("length", new FunctionDescription("Length", 1));
        
        //  replace readGlobalConstraint
        funcs.put("alldifferent", new FunctionDescription("AllDifferent", 1));
        funcs.put("allDiff", new FunctionDescription("AllDifferent", 1));
        funcs.put("gcc", new FunctionDescription("GlobalCard", 3));
        funcs.put("cumulative", new FunctionDescription("Cumulative", 4));
        
        // missing table
        funcs.put("atmost", new FunctionDescription("AtMost", 3));
        funcs.put("atleast", new FunctionDescription("AtLeast", 3));
        funcs.put("alldifferent_except", new FunctionDescription("AllDifferentExcept", 2));
        
        // replace some of readFunction
        funcs.put("factorial", new FunctionDescription("Factorial", 1));
        funcs.put("product", new FunctionDescription("TimesVector", 1));
        funcs.put("and", new FunctionDescription("AndVector", 1));
        funcs.put("or", new FunctionDescription("OrVector", 1));
        funcs.put("xor", new FunctionDescription("XorVector", 1));
        
        //  debug
        funcs.put("print", new FunctionDescription("Print", 1));
        
        // Conjure support
        funcs.put("catchUndef", new FunctionDescription("CatchUndef", 2));
        
        // SNS
        funcs.put("frameUpdate", new FunctionDescription("FrameUpdate", 4));
        
        // Types
        funcs.put("isRegular", new FunctionDescription("IsRegularMatrix", 1));
        
        //  Frequent itemset mining / multi-stage solving functions.
        funcs.put("dominance_relation", new FunctionDescription("DominanceRelation", 1));
        funcs.put("incomparability_function", new FunctionDescription("IncomparabilityFunction", 2));
        funcs.put("fromSolution", new FunctionDescription("FromSolution", 1));
        
        //  Special ones
        funcs.put("elementId", new FunctionDescription("ElementId", 2));
        funcs.put("amopb", new FunctionDescription("AMOPB", 3));
        funcs.put("eopb", new FunctionDescription("EOPB", 3));
    }
    
    /* ====================================================================
     read
    ==================================================================== */
    public Model readModel() {
        ASTNode constraints = null;
        ASTNode objective = null;
        m.global_symbols=new SymbolTable();
        
        try {
            tokens.mark("model1");            // This is not necessary, but puts in extra checks on reset stack.
            readHeader();
            tokens.commit("Read header line successfully.");
            readDeclarations();
            try {
                tokens.mark("model2");
                objective = readObjective();
                tokens.eraseMark("model2");
            } catch (EPrimeSyntaxException e) {
                tokens.reset("model2");
            }
            constraints = readConstraints();
            tokens.eraseMark("model1");
        } catch (EPrimeSyntaxException e) {
            tokens.reset("model1");
            CmdFlags.errorExit("Failed to read header line. Expected the following:  language ESSENCE' 1.0");
        }
        
        SNS snswrapper=null;
        if(incumbentmapping!=null) {
            snswrapper=new SNS(incumbentmapping, new Container(neighbourhoods), new NoValue(), new Container(groups));
        }
        m.setup(constraints, m.global_symbols, objective, branchingon, heuristic, snswrapper, preservevariables);  // Populate the model.
        return m;
    }
    
    /* ====================================================================
     Read a parameter file. Requires the model that was constructed
     when the model file was read. 
    ==================================================================== */

    public ArrayList<ASTNode> readParameterFile(Model _m) {
        m=_m;
        branchingon = null;
        heuristic = null;
        
        // Read the optional language line. 
        try {
            tokens.mark("paramhead");
            readHeader();
            tokens.eraseMark("paramhead");
            tokens.commit("Successfully parsed language line.");
        }
        catch (EPrimeSyntaxException e) {
            tokens.reset("paramhead");
        }
        
        
        ArrayList<ASTNode> paramlist = new ArrayList<ASTNode>();
        
        while (true) {
            try {
                tokens.mark("param");
                
                try {
                    tokens.mark("rpf");
                    ASTNode a = readLetting();
                    paramlist.add(a);
                    tokens.eraseMark("rpf");
                    tokens.commit("Successfully parsed letting statement.");
                } catch (EPrimeSyntaxException e) {
                    tokens.reset("rpf");
                    try {
                        tokens.mark("rpf2");
                        readHeuristic();
                        tokens.eraseMark("rpf2");
                        tokens.commit("Successfully parsed heuristic.");
                    } catch (EPrimeSyntaxException e2) {
                        tokens.reset("rpf2");
                        readBranchingOn();
                        tokens.commit("Successfully parsed branching on statement.");
                    }
                }
                
                tokens.eraseMark("param");
            } catch (EPrimeSyntaxException e2) {
                tokens.reset("param");
                break;
            }
        }
        
        // Try to read the next token and check if it is EOF. 
        try {
            tokens.nextToken();
            if (tokens.tokenType == EPrimeTokenizer.TT_EOF) {
                if (VB_MTDS) {
                    System.out.println("parameters read successfully");
                }
                
                if (heuristic != null) {
                    if (m.heuristic != null) {
                        CmdFlags.println("WARNING: Parameter file overrides 'heuristic' statement in model file.");
                    }
                    m.heuristic = heuristic;
                }
                if (branchingon != null) {
                    if (m.branchingon != null) {
                        CmdFlags.println("WARNING: Parameter file overrides 'branching on' statement in model file.");
                    }
                    m.branchingon = branchingon;
                }
                return paramlist;
            }
        }
        catch (EPrimeSyntaxException e2) {
        }
        
        // If next token is not EOF, or failed to read the next token, create an error message and quit. 
        tokens.raiseError();
        return null;
    }

    // Header & Declarations %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    /* ====================================================================
     readHeader()
	 Header ::= language (Essence | ESSENCE') <Int>.<Int>
	 NB This disallows the use of true/false as 1/0 in this position
    ==================================================================== */
    private void readHeader() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read header line");
        }
        readTerminalString("language");
        try {
            tokens.mark("ess");
            readTerminalStringPrime("ESSENCE'");
            tokens.eraseMark("ess");
        } catch (EPrimeSyntaxException Ozgur) {
            tokens.reset("ess");
            readTerminalString("Essence");
        }
        readPositiveInt();
        readTerminalString(".");
        readPositiveInt();
        if (VB_MTDS) {
            System.out.println("header line read successfully");
        }
    }

    /* ====================================================================
     readDeclarations()
     (<Given> | <Where> | <Letting> | <Find>)*
    ==================================================================== */
    private void readDeclarations() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read declarations");
        }
        while (true) {
            try {
                readDeclaration();
                tokens.commit("Successfully parsed declaration.");
            } catch (EPrimeSyntaxException e) {
                if (VB_MTDS) {
                    System.out.println("finished reading declarations");
                }
                return; 
            }
        }
    }

    /* ====================================================================
     readDeclaration()
     (<Given> | <Where> | <Letting> | <Find>)
    ==================================================================== */
    private void readDeclaration() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read a declaration");
        }
        try {
            tokens.mark();
            readGiven();
            tokens.eraseMark();
        } catch (EPrimeSyntaxException e2) {
            tokens.reset();
            try {
                tokens.mark();
                readWhere();
                tokens.eraseMark();
            } catch (EPrimeSyntaxException e3) {
                tokens.reset();
                try {
                    tokens.mark();
                    ASTNode let = readLetting();
                    tokens.eraseMark();
                    m.global_symbols.lettings_givens.add(let);
                } catch (EPrimeSyntaxException e4) {
                    tokens.reset();
                    try {
                        tokens.mark();
                        readFind();
                        tokens.eraseMark();
                    } catch (EPrimeSyntaxException e5) {
                        tokens.reset();
                        try {
                            tokens.mark();
                            readBranchingOn();
                            tokens.eraseMark();
                        } catch (EPrimeSyntaxException e6) {
                            tokens.reset();
                            try {
                                tokens.mark();
                                readHeuristic();
                                tokens.eraseMark();
                            } catch (EPrimeSyntaxException e7) {
                                tokens.reset();
                                try {
                                    tokens.mark("sns");
                                    readSNS();
                                    tokens.eraseMark("sns");
                                } catch (EPrimeSyntaxException e8) {
                                    tokens.reset("sns");
                                    try {
                                        tokens.mark("presvars");
                                        readPreserveVariables();
                                        tokens.eraseMark("presvars");
                                    }
                                    catch(EPrimeSyntaxException e9) {
                                        tokens.reset("presvars");
                                        throw new EPrimeSyntaxException("Expecting: Given, Where, Letting, Find, Branching on, Heuristic or preserveVariables statement. Found: "+ tokens.toString());
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        if (VB_MTDS) {
            System.out.println("declaration read successfully");
        }
    }

    /* ====================================================================
     readGiven()
     <Given> ::= "given" <IdList> : <Domain>
    ==================================================================== */
    private void readGiven() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read given");
        }
        readTerminalString("given");
        tokens.commit("Parsed 'given' keyword.");
        ASTNode a = readIdList();

        try {
            tokens.mark("given");
            readTerminalString(":");
            tokens.commit("Parsed 'given ... :'.");
            ASTNode d = readExpression();
            
            for (int i=0; i<a.numChildren(); i++) {
                m.global_symbols.lettings_givens.add(new Given(a.getChild(i), d));
            }
            tokens.eraseMark("given");
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("given");
            readTerminalString("new");
            readTerminalString("domain");
            readTerminalString("int");

            tokens.commit("Successfully parsed 'given ... new domain int'.");

            for(int i=0; i<a.numChildren(); i++) {
                m.global_symbols.lettings_givens.add(new Given(a.getChild(i), new IntegerDomain(new Range(null, null))));
            }
        }

        if (VB_MTDS) {
            System.out.println("given read successfully");
        }
    }

    /* ====================================================================
     readWhere()
	 where Expression
    ==================================================================== */
    private void readWhere() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read where");
        }
        readTerminalString("where");
        tokens.commit("Successfully parsed 'where' keyword.");
        ASTNode a = readExpression();
        if (VB_MTDS) {
            System.out.println("where read successfully");
        }
        m.global_symbols.lettings_givens.add(new Where(a));
    }

    /* ====================================================================
     readLetting()
     "letting" Identifier "be" "domain" Domain   |
     "letting" Identifier [ ":" Domain ] "be" Expression 
    ==================================================================== */
    private ASTNode readLetting() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read letting");
        }
        readTerminalString("letting");
        tokens.commit("Parsed 'letting' keyword.");
        ASTNode id = readIdentifier();
        tokens.commit("Parsed 'letting' keyword and identifier.");
        try {
            tokens.mark("rl");
            readTerminalString("be");
            readTerminalString("domain");
            tokens.commit("Successfully parsed 'letting ... be domain'.");
            ASTNode eq = readExpression();
            tokens.eraseMark("rl");
            if (VB_MTDS) {
                System.out.println("letting read successfully");
            }
            return new Letting(id, eq);
        } catch (EPrimeSyntaxException e) {
            tokens.reset("rl");

            // Parse optional domain specified with a :
            ASTNode dom;
            try {
                tokens.mark("rldom");
                readTerminalString(":");
                tokens.commit("Successfully parsed 'letting ... :'.");
                dom = readExpression();
                tokens.eraseMark("rldom");
            } catch (EPrimeSyntaxException e2) {
                tokens.reset("rldom");
                dom = null;
            }

            // New bit.
            try {
                tokens.mark("rlp");
                readTerminalString("be");
                tokens.eraseMark("rlp");
            } catch (EPrimeSyntaxException e1) {
                tokens.reset("rlp");
                readTerminalString("=");
            }

            tokens.commit("Successfully parsed 'letting ... be'.");

            // Optimisation -- first try the quick parser for big matrices of ints
            ASTNode eq = null;

            try {
                tokens.mark("quick");
                eq = readQuickConstantMatrixNotDeref();
                tokens.eraseMark("quick");
            } catch (EPrimeSyntaxException e1) {
                tokens.reset("quick");
            }

            if (eq == null) {
                eq = readExpression();
            }            // the general case.
            
            tokens.commit("Letting statement read successfully");
            
            if (VB_MTDS) {
                System.out.println("letting read successfully");
            }
            if (dom == null) {
                return new Letting(id, eq);
            } else {
                return new Letting(id, eq, dom);
            }
        }
    }

    /* ====================================================================
     readFind()
     <Find> ::= "find" <IdList> : { <Domain> | <Identifier> }
    ==================================================================== */
    private void readFind() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read find");
        }
        readTerminalString("find");
        tokens.commit("Parsed 'find' keyword.");
        ASTNode a = readIdList();
        tokens.commit("Parsed 'find' keyword and list of identifiers.");
        readTerminalString(":");
        tokens.commit("Parsed 'find ... :'.");
        ASTNode b = readExpression();
        
        for (int i=0; i<a.numChildren(); i++) {
            m.global_symbols.lettings_givens.add(new Find(a.getChild(i), b.copy()));
        }
        
        if (VB_MTDS) {
            System.out.println("find read successfully");
        }
    }

    /* ====================================================================
     readBranchingOn()
     <BranchingOn> ::= "branching" "on" "["  "]"
    ==================================================================== */
    private void readBranchingOn() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read branching on");
        }
        readTerminalString("branching");
        readTerminalString("on");
        tokens.commit("Parsed 'branching on'.");
        
        if (branchingon != null) {
            // Not really a syntax error
            throw new EPrimeSyntaxException("Expected at most one 'branching on' statement. Found a second 'branching on' statement.");
        }
        
        branchingon = readMagicList();
        
        if (VB_MTDS) {
            System.out.println("branching on read successfully");
        }
        
        
    }
    
    /* ====================================================================
     readPreserveVariables()
     As readBranchingOn, 
    ==================================================================== */
    private void readPreserveVariables() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read preserveVariables");
        }
        readTerminalString("preserveVariables");
        tokens.commit("Parsed 'preserveVariables'.");
        
        if (preservevariables != null) {
            // Not really a syntax error
            throw new EPrimeSyntaxException("Expected at most one 'preserveVariables' statement. Found a second 'preserveVariables' statement.");
        }
        
        preservevariables = readMagicList();
    }
    
    /* ====================================================================
     readMagicList()
     Read a list [a, b, c ...] where each element may have any number of
     dimensions. Flattens and concatenates everything into a 1-dimensional matrix. 
    ==================================================================== */
    private ASTNode readMagicList() throws EPrimeSyntaxException {
        readTerminalString("[");
        tokens.commit("Parsed '['.");
        ArrayList<ASTNode> list = new ArrayList<ASTNode>();
        
        while (true) {
            try {
                tokens.mark("bo");
                list.add(readExpression());
                tokens.eraseMark("bo");
                tokens.commit("Parsed entry in list.");
            } catch (EPrimeSyntaxException e) {
                tokens.reset("bo");
                break;
            }
            
            try {
                tokens.mark("comma");
                readTerminalString(",");
                tokens.eraseMark("comma");
                tokens.commit("Parsed ',' in list.");
            } catch (EPrimeSyntaxException e3) {
                tokens.reset("comma");
                break;                // If there's no comma, jump out. Allows a final comma before the square bracket.
            }
        }
        
        readTerminalString("]");
        
        for (int i =0; i < list.size(); i++) {
            if (list.get(i).getDimension() == 0) {
                ArrayList<ASTNode> tmp = new ArrayList<ASTNode>();
                tmp.add(list.get(i));
                list.set(i, new CompoundMatrix(tmp));
            }
            // flatten to 1 dimension.
            list.set(i, new Flatten(list.get(i)));
        }
        
        return new Cat(list);
    }
    
    /* ====================================================================
     readHeuristic()
     <Heuristic> ::= "heuristic" [ "sdf",  ]
    ==================================================================== */
    private void readHeuristic() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read heuristic");
        }
        readTerminalString("heuristic");
        tokens.commit("Successfully parsed 'heuristic' keyword.");
        String h = readTerminalString();
        String h2 = null;
        if (h.equals("static")) { h2 = "STATIC"; } else if (h.equals("sdf")) { h2 = "SDF"; } else if (h.equals("conflict")) { h2 = "CONFLICT"; } else if (h.equals("srf")) { h2 = "SRF"; }
        else if (h.equals("ldf")) { h2 = "LDF"; } else if (h.equals("wdeg")) { h2 = "WDEG"; }  else if (h.equals("domoverwdeg")) { h2 = "DOMOVERWDEG"; }

        if (h2 == null) {
            throw new EPrimeSyntaxException("Expected static, sdf, conflict srf, ldf, wdeg or domoverwdeg, found:"+h);
        }

        if (heuristic != null) {
            // Not really a syntax error
            throw new EPrimeSyntaxException("Expected at most one 'heuristic' statement. Found A second 'heuristic' statement.");
        }
        heuristic = h2;
    }
    
    /* ====================================================================
     readSNS()
    ==================================================================== */
    private void readSNS() throws EPrimeSyntaxException {
        try {
            tokens.mark("sns2");
            readTerminalString("SNSNeighbourhood");
            tokens.commit("Successfully parsed 'SNSNeighbourhood' keyword.");
            ASTNode[] args=new ASTNode[5];
            
            args[0] = readIdentifier();   //   Neighbourhood name.
            
            readTerminalString(":");
            //tokens.commit("Successfully parsed 'neighbourhood ... :'");
            readTerminalString("(");
            args[1] = readExpression(); // Size var  /// Should be an identifier or some other reference to a single variable/constant.
            readTerminalString(",");
            args[2]=readExpression(); // Activation var /// Should be an identifier or some other reference to a single variable/constant.
            readTerminalString(",");
            args[3]=readIdentifier();  // Group name
            readTerminalString(",");
            args[4]=readMagicList();   // Var list.
            readTerminalString(")");
            tokens.eraseMark("sns2");
            
            neighbourhoods.add(new SNSNeighbourhood(args));
        }
        catch (EPrimeSyntaxException e) {
            tokens.reset("sns2");
            try {
                tokens.mark("sns3");
                readTerminalString("SNSIncumbentMapping");
                tokens.commit("Successfully parsed 'SNSIncumbentMapping' keyword.");
                
                readTerminalString("(");
                ASTNode primaryvars=readMagicList();
                readTerminalString(",");
                ASTNode incumbentvars=readMagicList();
                readTerminalString(")");
                
                tokens.eraseMark("sns3");
                incumbentmapping=new SNSIncumbentMapping(m, primaryvars, incumbentvars);
            }
            catch (EPrimeSyntaxException e2) {
                tokens.reset("sns3");
                readTerminalString("SNSGroup");
                tokens.commit("Successfully parsed 'SNSGroup' keyword.");
                ASTNode groupname = readIdentifier();
                
                readTerminalString(":");
                
                ASTNode groupvars=readMagicList();
                groups.add(new SNSGroup(groupname, groupvars));
            }
        }
    }
    
    /* ====================================================================
     readSimpleDomainAtom()
	 SimpleDomain -> "bool"
	     | "int" [ "(" BoundedSetOfRanges ")" ]
	     | IdentifierString
	     
     Read a SimpleDomain that is atomic as far as domains are concerned.
     e.g. int(1, 3..5) or int() (which means the empty domain).
    ==================================================================== */

    private ASTNode readSimpleDomainAtom() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read SimpleDomainAtom");
        }

        try {
            tokens.mark("rsd");
            readTerminalString("bool");
            tokens.eraseMark("rsd");
            return new BooleanDomainFull();
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("rsd");
            try {
                tokens.mark("rsd2");
                readTerminalString("int");
                try {
                    tokens.mark("rsd3");
                    readTerminalString("(");
                    
                    ASTNode a;
                    
                    try {
                        tokens.mark("rsd5");
                        a = readUnboundedSetOfRanges();
                        tokens.eraseMark("rsd5");
                    } catch (EPrimeSyntaxException e2) {
                        tokens.reset("rsd5");
                        a = new IntegerDomain(new EmptyRange());                        /// Empty domain! "int()".
                    }
                    
                    readTerminalString(")");
                    tokens.eraseMark("rsd3");
                    tokens.eraseMark("rsd2");
                    return a;
                } catch (EPrimeSyntaxException e) {
                    tokens.reset("rsd3");
                }
                tokens.eraseMark("rsd2");
                return new IntegerDomain(new Range(null, null));                // Just "int", the set of all integers.
            } catch (EPrimeSyntaxException e2) {
                tokens.reset("rsd2");
                ASTNode st = readIdentifier();
                return st;
            }
        }
    }
    
    private ASTNode readMatrixDomain() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read MatrixDomain");
        }
        ArrayList<ASTNode> indices = new ArrayList<ASTNode>();
        readTerminalString("matrix");
        tokens.commit("Successfully parsed 'matrix' keyword.");
        
        // Keywords 'indexed by' are optional. 
        try {
            tokens.mark("indexedby");
            readTerminalString("indexed");
            readTerminalString("by");
            tokens.eraseMark("indexedby");
        }
        catch(EPrimeSyntaxException e1) {
            tokens.reset("indexedby");
        }
        
        tokens.commit("Successfully parsed 'matrix indexed by'.");
        readTerminalString("[");
        indices.add(readExpression());
        tokens.commit("Parsed 'matrix indexed by [...'.");
        while (true) {
            try {
                tokens.mark("rmdom");
                readTerminalString(",");
                tokens.commit("Parsed 'matrix indexed by [... ,'.");
                ASTNode a = readExpression();
                tokens.commit("Parsed 'matrix indexed by [...'.");
                tokens.eraseMark("rmdom");
                indices.add(a);
            } catch (EPrimeSyntaxException e1) {
                tokens.reset("rmdom");
                break;
            }
        }
        
        readTerminalString("]");
        readTerminalString("of");
        tokens.commit("Successfully parsed 'matrix indexed by ... of'.");
        ASTNode base = readExpression();
        
        if (VB_MTDS) System.out.println("MatrixDomain read successfully");
        return new MatrixDomain(base, indices);
    }

    // Objective & Constraints %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    /* ====================================================================
     readObjective()
	 Objective ::= maximising <ArithExpr> | minimising <ArithExpr>
    ==================================================================== */
    private ASTNode readObjective() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read objective");
        }
        ASTNode ob = null;
        try {
            tokens.mark();
            ob = readMaximising();
            tokens.eraseMark();
        } catch (EPrimeSyntaxException e) {
            tokens.reset();
            try {
                tokens.mark();
                ob = readMinimising();
                tokens.eraseMark();
            } catch (EPrimeSyntaxException e2) {
                tokens.reset();
                throw new EPrimeSyntaxException("Expected objective, found: "+tokens.token);
            }
        }
        if (VB_MTDS) {
            System.out.println("objective read successfully: " + ob);
        }
        return ob;
    }

    /* ====================================================================
     readMinimising()
     <Minimising> ::= "minimising" <AtomicId>
    ==================================================================== */
    private ASTNode readMinimising() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read minimizing");
        }
        readTerminalString("minimising");
        tokens.commit("Successfully parsed 'minimising' keyword.");
        ASTNode a = readExpression();
        if (VB_MTDS) {
            System.out.println("read minimizing successfully");
        }
        return new Minimising(a);
    }

    /* ====================================================================
     readMaximising()
     <maximising> ::= "maximising" <ArithmeticExpression>
    ==================================================================== */
    private ASTNode readMaximising() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read maximizing");
        }
        readTerminalString("maximising");
        tokens.commit("Successfully parsed 'maximising' keyword.");
        ASTNode a = readExpression();
        if (VB_MTDS) {
            System.out.println("read maximizing successfully");
        }
        return new Maximising(a);
    }

    /* ====================================================================
     readConstraints()
	 <Constraints> ::= "such that" {<Constraint>}*
    ==================================================================== */
    private ASTNode readConstraints() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read constraints");
        }
        readTerminalString("such");
        readTerminalString("that");
        tokens.commit("Successfully parsed 'such that'.");
        // Make a single And for all the constraints.
        
        ArrayList<ASTNode> andlist = new ArrayList<ASTNode>();
        try {
            tokens.mark("con1");
            andlist.add(readExpression());
            tokens.eraseMark("con1");
            while (true) {
                try {
                    tokens.mark("con2");
                    readTerminalString(",");
                    tokens.commit("Parsed comma.");
                    andlist.add(readExpression());
                    tokens.eraseMark("con2");
                } catch (EPrimeSyntaxException e2) {
                    tokens.reset("con2");
                    break;
                }
            }
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("con1");
        }

        tokens.nextToken();
        if (tokens.tokenType == EPrimeTokenizer.TT_EOF) {
            if (VB_MTDS) {
                System.out.println("constraints read successfully");
            }
            return new Top(new And(andlist));            // Wrap it in a Top.
        }
        throw new EPrimeSyntaxException("Expected constraint, found: "+tokens.toString());
    }
    
    // Expressions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    /* ====================================================================
     readExpression()
     Expression -> PartExpression {BinOp PartExpression}*
    ==================================================================== */

    private ASTNode readExpression() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read Expression");
        }
        // List of expressions [Part,BinOp, Part ....].
        ArrayList<ASTNode> exlist = new ArrayList<ASTNode>();
        
        exlist.add(readPartExpression());
        tokens.commit("Successfully read part expression:" + exlist.get(0));
        while (true) {
            try {
                tokens.mark("inreadexpression");
                if (VB_MTDS) {
                    System.out.println("attempting to read a binop then partexpression");
                }
                ASTNode a = readBinOp();
                tokens.commit("Successfully read binop:" + a);
                ASTNode b = readPartExpression();
                tokens.commit("Successfully read part expression:" + b);
                if (VB_MTDS) {
                    System.out.println("succeeded read a binop then partexpression " + a + ", " + b);
                }
                tokens.eraseMark("inreadexpression");
                exlist.add(a); exlist.add(b);                // Make sure both are read successfully before adding them to list.
            } catch (EPrimeSyntaxException e) {
                tokens.reset("inreadexpression");
                break;
            }
        }
        if (VB_MTDS) {
            System.out.println("succeeded reading Expression");
        }
        // return new Expression(exlist);
        if (VB_MTDS) {
            System.out.println("Converting list:" + exlist);
        }
        ShuntingYard sy = new ShuntingYard();
        ASTNode a = sy.convertToTree(exlist);
        if (VB_MTDS) {
            System.out.println("Converted to tree:" + a);
        }
        return a;
    }

    /* ====================================================================
    readPartExpression()
    "(" Expression ")"  |
    UnaryExpression |
    GlobalConstraint |
    QuantifiedExpression |
    ArrayExpression | 
    AtomicExpression 
    
    
    ==================================================================== */

    private ASTNode readPartExpression() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read PartExpression");
        }
        ASTNode a;
        try {
            tokens.mark("matdom");
            a = readMatrixDomain();   //  Must parse this first, otherwise 'matrix' will be parsed as an identifier.
            tokens.eraseMark("matdom");
        } catch (EPrimeSyntaxException md) {
            tokens.reset("matdom");
            try {
                tokens.mark("rpe");
                a = readBracketedExpression();
                tokens.eraseMark("rpe");
            } catch (EPrimeSyntaxException e1) {
                tokens.reset("rpe");
                try {
                    tokens.mark("rpe2");
                    a = readUnaryExpression();
                    tokens.eraseMark("rpe2");
                } catch (EPrimeSyntaxException e2) {
                    tokens.reset("rpe2");
                    try {
                        tokens.mark("rpe3");
                        a = readConstant();
                        tokens.eraseMark("rpe3");
                    } catch (EPrimeSyntaxException e3) {
                        tokens.reset("rpe3");
                        try {
                            tokens.mark("rpe4");
                            a = readGlobalConstraint();
                            tokens.eraseMark("rpe4");
                        } catch (EPrimeSyntaxException e4) {
                            tokens.reset("rpe4");
                            try {
                                tokens.mark("rpe5");
                                a = readQuantifiedExpression();
                                tokens.eraseMark("rpe5");
                            } catch (EPrimeSyntaxException e5) {
                                tokens.reset("rpe5");
                                try {
                                    tokens.mark("rpe6");
                                    a = readArrayExpression();   // Includes bare identifier, matrix deref, matrix slice.
                                    tokens.eraseMark("rpe6");
                                } catch (EPrimeSyntaxException e6) {
                                    tokens.reset("rpe6");
                                    try {
                                        tokens.mark("rpe7");
                                        a=readSetComprehensionOrLiteral();
                                        tokens.eraseMark("rpe7");
                                    } catch (EPrimeSyntaxException e7) {
                                        tokens.reset("rpe7");
                                        a=readSimpleDomainAtom();
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        
        // Optionally followed by slices/deref.  Need to take this out of the above, e.g. readArrayExpression.
        try {
            tokens.mark("slice");
            a = readSliceOrDeref(a);
            tokens.eraseMark("slice");
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("slice");
        }
        
        if (VB_MTDS) {
            System.out.println("succeeded reading PartExpression");
        }
        return a;
    }
    
    private ASTNode readBracketedExpression() throws EPrimeSyntaxException {
        readTerminalString("(");
        ASTNode a=readExpression();
        readTerminalString(")");
        
        a=new Brackets(a);  // Wrap in the temporary Brackets type
        
        //  In case it is a bracketed matrix expression, it may be followed by a slice or deref. 
        try {
            tokens.mark("slice");
            a = readSliceOrDeref(a);
            tokens.eraseMark("slice");
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("slice");
        }
        return a;
    }
    
    /* ====================================================================
	 readUnaryExpression()
	 "!" Expression  | "-" Expression  | "|" Expression "|"  
    ==================================================================== */
    private ASTNode readUnaryExpression() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read UnaryExpression");
        }
        try {
            tokens.mark("not");
            readTerminalString("!");
            tokens.commit("Read '!' (negation)");
            ASTNode a = readPartExpression();
            tokens.eraseMark("not");
            return new Negate(a);
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("not");
            try {
                tokens.mark("unaryminus");
                readTerminalString("-");
                tokens.commit("Read '-' (unary minus)");
                ASTNode a = readPartExpression();
                
                // One attempt to make unary minus work correctly with power. Parse all powers after the unary minus and build the tree here.
                // Only works because power has the highest precedence of all the binary operators. Otherwise it would interfere with parsing other operators.
                
                ArrayList<ASTNode> listpow = new ArrayList<ASTNode>();
                
                while (true) {
                    try {
                        tokens.mark("trypow");
                        readTerminalString("**");
                        tokens.commit("Read '**' (power)");
                        listpow.add(readPartExpression());
                        tokens.eraseMark("trypow");
                    } catch (EPrimeSyntaxException epow) {
                        tokens.reset("trypow");
                        break;                        // exit the loop.
                    }
                }
                tokens.eraseMark("unaryminus");
                if (listpow.size() > 0) {
                    // Build a tree of power
                    ASTNode tree = listpow.get(listpow.size() - 1);
                    listpow.remove(listpow.size() - 1);
                    
                    while (listpow.size() > 0) {
                        tree = new Power(listpow.get(listpow.size() - 1), tree);
                        listpow.remove(listpow.size() - 1);
                    }
                    
                    tree = new Power(a, tree);
                    return new UnaryMinus(tree);

                } else {
                    return new UnaryMinus(a);                    // The simple case.
                }
            } catch (EPrimeSyntaxException e2) {
                tokens.reset("unaryminus");
                readTerminalString("|");
                tokens.commit("Read '|' (absolute value)");
                ASTNode a = readExpression();
                readTerminalString("|");
                return new Absolute(a);
            }
        }
        // if (VB_MTDS) System.out.println("succeeded reading UnaryExpression") ;
    }
    
    /* ====================================================================
     readGlobalConstraint()
	 alldifferent "(" ArrayExpression ")"
     gcc "("    ")
     | table "(" ArrayExpression "," "[" Tuple "," Tuple ....  [","]  "]" ")"
     | atmost "(" ArrayExpression "," ArrayExpression "," ArrayExpression ")"
    ==================================================================== */
    private ASTNode readGlobalConstraint() throws EPrimeSyntaxException {
        try {
            tokens.mark("readtab");
            ASTNode a = readTableConstraint();
            tokens.eraseMark("readtab");
            return a;
        } catch (EPrimeSyntaxException e3) {
            tokens.reset("readtab");
            
            try {
                tokens.mark("func");
                ASTNode f = readFunction();
                tokens.eraseMark("func");
                return f;
            } catch (EPrimeSyntaxException e7) {
                tokens.reset("func");
                ASTNode f2=readFunctionGeneric();
                return f2;
            }
        }
    }
    
    private ASTNode readFunction() throws EPrimeSyntaxException {
        try {
            tokens.mark("min");
            readTerminalString("min");
            tokens.commit("Parsed keyword 'min'");
            tokens.eraseMark("min");

            readTerminalString("(");
            ASTNode a = readExpression();
            boolean comma = tryReadTerminalString(",");

            if (comma) {
                ASTNode b = readExpression();
                readTerminalString(")");
                return new Min(a, b);
            } else {
                readTerminalString(")");
                return new MinVector(a);
            }
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("min");
            try {
                tokens.mark("max");
                readTerminalString("max");
                tokens.commit("Parsed keyword 'max'");
                tokens.eraseMark("max");

                readTerminalString("(");
                ASTNode a = readExpression();
                boolean comma = tryReadTerminalString(",");

                if (comma) {
                    ASTNode b = readExpression();
                    readTerminalString(")");
                    return new Max(a, b);
                } else {
                    readTerminalString(")");
                    return new MaxVector(a);
                }
            } catch (EPrimeSyntaxException e2) {
                tokens.reset("max");
                
                // sum function.
                readTerminalString("sum");
                readTerminalString("(");
                tokens.commit("Parsed keyword 'sum'");       // Unusual one --- after bracket in case 'sum' belongs to a quantifier.
                ASTNode a = readArrayExpression();
                readTerminalString(")");
                return new SumVector(a);
            }
        }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Read functions where the name of the function
    //   is not overloaded (as, for example, min and max are). 
    
    private ASTNode readFunctionGeneric() throws EPrimeSyntaxException {
        tokens.mark("readfuncg");
        
        try {
            String s=readTerminalString();
            
            if(! funcs.containsKey(s)) {
                throw new EPrimeSyntaxException("Expected generic Function, found something unknown.");
            }
            
            FunctionDescription f=funcs.get(s);
            
            readTerminalString("(");
            tokens.commit("Parsed function name "+s+" and open bracket.");
            
            ASTNode slot1=readExpression();
            
            ASTNode slot2=null;
            ASTNode slot3=null;
            ASTNode slot4=null;
            
            if(f.numArgs>1) {
                readTerminalString(",");
                slot2=readExpression();
                
                if(f.numArgs>2) {
                    readTerminalString(",");
                    slot3=readExpression();
                }
                
                if(f.numArgs>3) {
                    readTerminalString(",");
                    slot4=readExpression();
                }
            }
            
            readTerminalString(")");
            
            ASTNode func=f.construct(slot1, slot2, slot3, slot4);
            
            tokens.eraseMark("readfuncg");
            
            return func;
        }
        catch (EPrimeSyntaxException e) {
            tokens.reset("readfuncg");
            throw e;
        }
    }
    
    private ASTNode readTableConstraint() throws EPrimeSyntaxException {
        try {
            tokens.mark("tab");
            readTerminalString("table");
            tokens.commit("Parsed keyword 'table'");
            readTerminalString("(");
            ASTNode vars = readArrayExpression();
            readTerminalString(",");
            tokens.commit("Parsed 'table(...,', expecting matrix of satisfying tuples.");
            ASTNode tups;
            try {
                // try to read a bracketed list of tuples with the old [<...>,<...>] syntax.
                tokens.mark("tableinner");
                readTerminalString("[");
                // read any number of tuples.
                ArrayList<ASTNode> tuples = new ArrayList<ASTNode>();
                while (true) {
                    try {
                        tokens.mark();
                        tuples.add(readTuple());
                        tokens.eraseMark();
                    } catch (EPrimeSyntaxException e3) {
                        tokens.reset();
                        break;
                    }
                    try {
                        tokens.mark();
                        readTerminalString(",");
                        tokens.eraseMark();
                    } catch (EPrimeSyntaxException e3) {
                        tokens.reset();
                        break;                    // If there's no comma, jump out. Allows a final comma before the square bracket.
                    }
                }
                readTerminalString("]");
                tokens.eraseMark("tableinner");
                tups = CompoundMatrix.make(tuples);
            } catch (EPrimeSyntaxException e5) {
                tokens.reset("tableinner");
                tups = readArrayExpression();
            }
            readTerminalString(")");
            tokens.eraseMark("tab");
            return new Table(m, vars, tups);
        }
        catch (EPrimeSyntaxException e6) {
            tokens.reset("tab");
            
            readTerminalString("tableshort");
            tokens.commit("Parsed keyword 'tableshort'");
            readTerminalString("(");
            ASTNode vars = readArrayExpression();
            readTerminalString(",");
            ASTNode tups = readArrayExpression();
            readTerminalString(")");
            
            return new TableShort(m, vars, tups);
        }
    }

    /* ====================================================================
     readQuantifiedExpression()
     quantifier IdList ":" BoundedDomain "." expression
    ==================================================================== */
    private ASTNode readQuantifiedExpression() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read quantified expression");
        }
        int qtype;        // 1,2,3 for forall, exists, sum
        try {
            tokens.mark();

            // either read forall or forAll (new spelling)
            try {
                tokens.mark("forall");
                readTerminalString("forall");
                tokens.eraseMark("forall");
            } catch (EPrimeSyntaxException f1) {
                tokens.reset("forall");
                readTerminalString("forAll");
            }

            tokens.eraseMark();
            qtype = 1;
        } catch (EPrimeSyntaxException e1) {
            tokens.reset();
            try {
                tokens.mark();
                readTerminalString("exists");
                tokens.eraseMark();
                qtype = 2;
            } catch (EPrimeSyntaxException e2) {
                tokens.reset();
                readTerminalString("sum");
                qtype = 3;
            }
        }

        ASTNode idlist = readIdList();
        readTerminalString(":");
        ASTNode domain = readExpression();
        readTerminalString(".");
        ASTNode qexpression = readExpression();
        if (VB_MTDS) {
            System.out.println("quantified expression read successfully");
        }

        // Wrap qexpression
        for (int i = idlist.numChildren() - 1; i >= 0; i--) {
            if (qtype == 1) {
                qexpression = new ForallExpression(idlist.getChild(i), domain, qexpression);
            } else if (qtype == 2) {
                qexpression = new ExistsExpression(idlist.getChild(i), domain, qexpression);
            } else {
                assert qtype == 3;
                qexpression = new QuantifiedSum(idlist.getChild(i), domain, qexpression);
            }
        }
        return qexpression;
    }

    // To be called directly after parsing an array expression of any kind.
    // Checks if the following token is "[", and if so, attempts to parse a
    // slice or deref. Recurses until there are no more slices/derefs.
    private ASTNode readSliceOrDeref(ASTNode arrayexp) throws EPrimeSyntaxException {
        readTerminalString("[");
        tokens.commit("Parsed '[' (start of matrix deref or slice)");

        ArrayList<ASTNode> r = readSliceRangeList();
        readTerminalString("]");

        boolean matrixslice = false;
        for (ASTNode a : r) {
            if (a.isSet()) {                // If any entry is not just a value but a set..
                matrixslice = true;
                break;
            }
        }

        ASTNode newex;
        if (matrixslice) {
            tokens.commit("Parsed ']' (end of matrix slice)");
            newex = new MatrixSlice(m, arrayexp, r);
        } else {
            tokens.commit("Parsed ']' (end of matrix deref)");
            newex = new MatrixDeref(arrayexp, r);
        }

        // Finally if this is a matrix slice, then need to recurse because it could
        // be followed by another matrix slice or deref.
        if (matrixslice) {
            try {
                tokens.mark("readslicerecurse");
                newex = readSliceOrDeref(newex);
                tokens.eraseMark("readslicerecurse");
            } catch (EPrimeSyntaxException e1) {
                tokens.reset("readslicerecurse");
            }
        }

        return newex;
    }

    /* =================================================================
    Either read an array function (at the moment just flatten) or an 
    array of some kind by calling readArrayExpressionInner,
    or a MatrixDeref because syntactically it is a MatrixSlice.
    ================================================================= */

    private ASTNode readArrayExpression() throws EPrimeSyntaxException {
        ASTNode arrayex;
        try {
            tokens.mark("arrayfunc");
            arrayex = readArrayFunction();
            tokens.eraseMark("arrayfunc");
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("arrayfunc");
            try {
                tokens.mark("arrayvarious");
                arrayex = readArrayExpressionInner();
                tokens.eraseMark("arrayvarious");
            }
            catch (EPrimeSyntaxException e2) {
                tokens.reset("arrayvarious");
                readTerminalString("(");
                arrayex=readArrayExpression();
                readTerminalString(")");
            }
        }
        
        // Optionally followed by slices/deref
        try {
            tokens.mark("slice");
            arrayex = readSliceOrDeref(arrayex);
            tokens.eraseMark("slice");
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("slice");
        }
        
        return arrayex;
    }

    /* ==================================================================
    Parse named functions that return arrays. 
    ===================================================================== */

    private ASTNode readArrayFunction() throws EPrimeSyntaxException {
        try {
            tokens.mark("flat");
            readTerminalString("flatten");
            readTerminalString("(");
            tokens.commit("Read flatten(");
            try {
                tokens.mark("flat2");
                ASTNode a = readArrayExpression();
                readTerminalString(")");
                tokens.eraseMark("flat2");
                tokens.eraseMark("flat");
                return new Flatten(a);
            }
            catch(EPrimeSyntaxException e) {
                tokens.reset("flat2");
                long dim=readPositiveInt();
                if(dim<1) {
                    throw new EPrimeSyntaxException("Expected integer >=1 in flatten, found: "+String.valueOf(dim));
                }
                readTerminalString(",");
                ASTNode a = readArrayExpression();
                readTerminalString(")");
                
                tokens.eraseMark("flat");
                
                while(dim>0) {
                    a=new ConcatenateMatrix(a);
                    dim--;
                }
                return a;
            }
        }
        catch(EPrimeSyntaxException e) {
            tokens.reset("flat");
            
            try {
                tokens.mark("cat");
                readTerminalString("cat");
                readTerminalString("(");
                tokens.commit("Read cat(");
                
                ArrayList<ASTNode> l=readCommaSeparatedList();
                
                readTerminalString(")");
                tokens.eraseMark("cat");
                
                return new Cat(l);
            }
            catch(EPrimeSyntaxException e2) {
                tokens.reset("cat");
                
                try {
                    tokens.mark("list");
                    readTerminalString("list");
                    readTerminalString("(");
                    tokens.commit("Read list(");
                    
                    ArrayList<ASTNode> l=readCommaSeparatedList();
                    
                    readTerminalString(")");
                    tokens.eraseMark("list");
                    
                    return new ListFunction(l);
                }
                catch(EPrimeSyntaxException e3) {
                    tokens.reset("list");
                    return readFunctionGeneric();
                }
            }
        }
    }
    
    //  Read a comma-separated list of expressions, of any length, with optional trailing comma. 
    private ArrayList<ASTNode> readCommaSeparatedList() throws EPrimeSyntaxException {
        ArrayList<ASTNode> l = new ArrayList<>();
        
        try {
            tokens.mark("readexp");
            ASTNode a = readPartExpression();
            l.add(a);
            tokens.eraseMark("readexp");
            tokens.commit("Read expression in comma-separated list of arguments.");
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("readexp");
            return l;
        }
        
        try {            // Optional suffix
            tokens.mark("rrl");
            readTerminalString(",");
            tokens.commit("Read ',' in comma-separated list of arguments.");
            l.addAll(readCommaSeparatedList());
            tokens.eraseMark("rrl");
        } catch (EPrimeSyntaxException e) {
            tokens.reset("rrl");
        }
        return l;
    }
    
    /* ====================================================================
     readArrayExpressionInner()
     Reads an individual id or matrix slice or construction 
     of a matrix from a list of expressions. 
    ==================================================================== */

    private ASTNode readArrayExpressionInner() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read array expression");
        }

        ASTNode arrayex;
        try {
            tokens.mark("comparray");
            arrayex = readCompoundOrComprehensionArrayExpression();
            tokens.eraseMark("comparray");
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("comparray");
            arrayex = readIdentifier();
        }

        if (VB_MTDS) {
            System.out.println("succeeded reading array expression: " + arrayex);
        }
        return arrayex;
    }

    /* ====================================================================
     readSliceRangeList()
     Either .. or an expression. 
    ==================================================================== */
    private ArrayList<ASTNode> readSliceRangeList() throws EPrimeSyntaxException {
        ArrayList<ASTNode> l = new ArrayList<>();

        try {
            tokens.mark("readdotdot");
            readTerminalString("..");
            l.add(new IntegerDomain(new Range(null, null)));
            tokens.eraseMark("readdotdot");
            tokens.commit("Read '..' in matrix slice or deref.");
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("readdotdot");
            l.add(readExpression());            // Any value.
        }

        try {            // Optional suffix
            tokens.mark("rrl");
            readTerminalString(",");
            tokens.commit("Read ',' in matrix slice or deref.");
            l.addAll(readSliceRangeList());
            tokens.eraseMark("rrl");
        } catch (EPrimeSyntaxException e) {
            if (VB_MTDS) {
                System.out.println("is not a SliceRangeList");
            }
            tokens.reset("rrl");
        }
        return l;
        // if (VB_MTDS) System.out.println("RangeList read successfully") ;
    }

    private ASTNode readCompoundOrComprehensionArrayExpression() throws EPrimeSyntaxException {
        // This function used to simply branch for either compound or comprehension matrix.
        // However, this backtracks over the first expression inside the matrix:
        // "[" e1 "|"   or   "[" e1 ","
        // Now it behaves like the compound matrix parser until it hits the first case
        // above, and if it does so it jumps into the comprehension parser.

        readTerminalString("[");
        tokens.commit("Parsed '[' (start of matrix literal or matrix comprehension)");
        
        //  If it is an empty matrix, optionally read a matrix domain type. 
        try {
            tokens.mark("emptymatrix");
            readTerminalString("]");
            
            tokens.commit("Parsed '[ ]' (empty matrix)");
            
            try {
                tokens.mark("empty2");
                readTerminalString(":");
                tokens.commit("Parsed '[ ] :' (empty matrix with type annotation)");
                readTerminalString("`");
                tokens.commit("Parsed '[ ] : `' (empty matrix with type annotation)");
                ASTNode md=readMatrixDomain();
                readTerminalString("`");
                tokens.eraseMark("empty2");
                tokens.eraseMark("emptymatrix");
                return new EmptyMatrix(md);
            }
            catch (EPrimeSyntaxException e2) {
                tokens.reset("empty2");
            }
            
            tokens.eraseMark("emptymatrix");
            return CompoundMatrix.make(new ArrayList<ASTNode>());
        }
        catch(EPrimeSyntaxException e1) {
            tokens.reset("emptymatrix");
        }
        
        boolean nocomma = false;

        ArrayList<ASTNode> l = new ArrayList<ASTNode>();
        while (true) {
            try {
                tokens.mark();
                ASTNode a = readExpression();
                tokens.eraseMark();
                l.add(a);
                if(l.size()==1) {
                    tokens.commit("Parsed first element in matrix literal or comprehension.");
                }
                else {
                    tokens.commit("Parsed element in matrix literal.");
                }
            } catch (EPrimeSyntaxException e2) {
                tokens.reset();
                break;
            }

            nocomma = ! tryReadTerminalString(",");
            if (nocomma) {
                break;
            }
            else {
                tokens.commit("Parsed ',' in matrix literal or comprehension.");
            }
        }

        if (nocomma && l.size() == 1) {
            // Parsed one expression and then failed to parse a comma.
            // Test for |
            boolean bar = tryReadTerminalString("|");
            if (bar) {
                tokens.commit("Parsed '|' (in comprehension)");
                // Jump into matrix comprehension parser.
                return readComprehensionInner(l.get(0));
            }
        }

        ASTNode dom = null;
        try {
            tokens.mark("optdom");
            readTerminalString(";");
            dom = readExpression();
            tokens.eraseMark("optdom");
        } catch (EPrimeSyntaxException e3) {
            tokens.reset("optdom");
        }

        readTerminalString("]");
        // Compound Matrices are indexed from 1 by default.
        if (dom == null) {
            return CompoundMatrix.make(l);
        } else {
            return CompoundMatrix.make(dom, l, false);
        }
    }

    private ASTNode readComprehensionInner(ASTNode innerexp) throws EPrimeSyntaxException {
        // Read quantifiers.
        ArrayList<ASTNode> quantifiers = new ArrayList<ASTNode>();
        boolean first = true;
        while (true) {
            try {
                tokens.mark("cquant");
                if (!first) {
                    readTerminalString(",");
                }
                
                ASTNode ids = readIdList();
                
                readTerminalString(":");
                
                ASTNode domain = readExpression();
                
                tokens.eraseMark("cquant");
                for (int i =0; i < ids.numChildren(); i++) {
                    quantifiers.add(new ComprehensionForall(ids.getChild(i), domain));
                }
                first = false;
            } catch (EPrimeSyntaxException e2) {
                tokens.reset("cquant");
                break;
            }
        }
        
        // Now read conditions.
        ArrayList<ASTNode> conditions = new ArrayList<ASTNode>();
        while (true) {
            try {
                tokens.mark("ccond");
                if (!first) {
                    readTerminalString(",");
                }

                ASTNode condition = readExpression();

                tokens.eraseMark("ccond");
                conditions.add(condition);
                first = false;
            } catch (EPrimeSyntaxException e2) {
                tokens.reset("ccond");
                break;
            }
        }

        ASTNode dom = null;
        try {
            tokens.mark("optdom");
            readTerminalString(";");
            dom = readExpression();
            tokens.eraseMark("optdom");
        } catch (EPrimeSyntaxException e3) {
            tokens.reset("optdom");
        }

        readTerminalString("]");
        if (dom == null) {
            return new ComprehensionMatrix(innerexp, quantifiers, new And(conditions));
        } else {
            return new ComprehensionMatrix(innerexp, quantifiers, new And(conditions), dom);
        }
    }

    ////////////////////////////////////////////////////////////////////////////// 
    // 
    // Optimisation -- reading large matrices of numbers typically in a letting.
    // Fails if it is anything other than a matrix of numbers.
    // Also fails if the matrix is followed by a "[" because this case should
    // be read somewhere else.

    private ASTNode readQuickConstantMatrixNotDeref() throws EPrimeSyntaxException {

        ASTNode m = readQuickConstantMatrix();

        // check there is no "[" following.
        tokens.mark("brac");
        boolean flag = false;
        try {
            readTerminalString("[");
            flag = true;
        } catch (EPrimeSyntaxException e) { }

        tokens.reset("brac");

        if (flag) {
            throw new EPrimeSyntaxException("Expected simple matrix, found matrix deref");
        } else {
            return m;
        }
    }

    private ASTNode readQuickConstantMatrix() throws EPrimeSyntaxException {
        // read some number of [
        readTerminalString("[");

        ArrayList<ASTNode> l = new ArrayList<ASTNode>();
        while (true) {

            // read a nested matrix or an integer.
            try {
                tokens.mark();
                long a = readPositiveInt();
                tokens.eraseMark();
                l.add(NumberConstant.make(a));

            } catch (EPrimeSyntaxException e2) {
                tokens.reset();
                try {
                    tokens.mark("nested");
                    ASTNode a = readQuickConstantMatrix();
                    tokens.eraseMark("nested");
                    l.add(a);
                } catch (EPrimeSyntaxException e3) {
                    tokens.reset("nested");
                    break;
                }
            }

            // read a comma
            try {
                tokens.mark();
                readTerminalString(",");
                tokens.eraseMark();
            } catch (EPrimeSyntaxException e2) {
                tokens.reset();
                break;
            }
        }

        readTerminalString("]");
        // Compound Matrices are indexed from 1 by default.
        return CompoundMatrix.make(l);
    }

    // Ranges %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    /* ====================================================================
     readRangeList()
     <RangeList> ::= <OpenRange> ["," <RangeList>]
    ==================================================================== */
    private ArrayList<ASTNode> readRangeList() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read RangeList");
        }
        ASTNode a = readOpenRange();
        ArrayList<ASTNode> l = new ArrayList<ASTNode>();
        l.add(a);
        try {            // Optional suffix
            tokens.mark("rrl");
            readTerminalString(",");
            l.addAll(readRangeList());
            tokens.eraseMark("rrl");
        } catch (EPrimeSyntaxException e) {
            if (VB_MTDS) {
                System.out.println("is not a RangeList");
            }
            tokens.reset("rrl");
        }
        return l;
        // if (VB_MTDS) System.out.println("RangeList read successfully") ;
    }

    /* ====================================================================
	 readOpenRange()
	 <OpenRange>    ::= <ClosedRange> |  ".." | <ArithExpr> ".." | ".."  
	 <ArithExpr>
    ==================================================================== */
    private ASTNode readOpenRange() throws EPrimeSyntaxException {
        boolean startdots = tryReadTerminalString("..");

        if (startdots) {
            try {
                tokens.mark("oprange");
                ASTNode right = readExpression();
                tokens.eraseMark("oprange");
                return new Range(null, right);
            } catch (EPrimeSyntaxException e1) {
                tokens.reset("oprange");
                return new Range(null, null);
            }
        } else {
            ASTNode left = readExpression();

            boolean middots = tryReadTerminalString("..");
            if (middots) {
                try {
                    tokens.mark("oprange2");
                    ASTNode right = readExpression();
                    tokens.eraseMark("oprange2");
                    return new Range(left, right);
                } catch (EPrimeSyntaxException e1) {
                    tokens.reset("oprange2");
                    return new Range(left, null);
                }
            } else {
                return left;
            }
        }
    }

    // Ops %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


    /* ====================================================================
     readBinOp()
     <BinOp> ::= + - / * ** %       
     \/  /\  =>  <=>        ->  <->
     = != <= < >= > <lex <=lex >lex >=lex in
     union intersect subset subsetEq superset supersetEq (set operators, as well as -)
    ==================================================================== */
    
    private ASTNode readBinOp() throws EPrimeSyntaxException {
        tokens.nextToken();
        if (tokens.tokenType != EPrimeTokenizer.TT_WORD && tokens.tokenType != EPrimeTokenizer.TT_OTHER) {
            throw new EPrimeSyntaxException("Expected binary operator, found: "+tokens.token);
        }
        
        if (!binops.contains(tokens.token)) {
            throw new EPrimeSyntaxException("Expected binary operator, found: "+tokens.token);
        }
        return new BinOpPlaceholder(tokens.token);
    }
    
    // Identifiers %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    /* ====================================================================
     readIdList()
     <IdList> ::= Identifier ["," <IdList>]
    ==================================================================== */
    private ASTNode readIdList() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read IdList");
        }
        ArrayList<ASTNode> theList = new ArrayList<ASTNode>();
        theList.add(readIdentifier());
        while (true) {
            try {
                tokens.mark("readidlist");
                readTerminalString(",");
                theList.add(readIdentifier());
                tokens.eraseMark("readidlist");
            } catch (EPrimeSyntaxException e) {
                tokens.reset("readidlist");
                break;
            }
        }        // end of while loop
        if (VB_MTDS) {
            System.out.println("IdList read successfully");
        }
        return new Container(theList);
    }

    /* ====================================================================
     readTuple()
     read a tuple of constants like <1,2,3>. Old syntax, only used in table constraint. 
    ==================================================================== */
    private ASTNode readTuple() throws EPrimeSyntaxException {
        readTerminalString("<");
        ArrayList<ASTNode> tupleContents = new ArrayList<ASTNode>();
        while (true) {
            try {
                tokens.mark();
                tupleContents.add(readConstant());
                tokens.eraseMark();
            } catch (EPrimeSyntaxException e1) {
                tokens.reset();
                break;
            }
            try {
                tokens.mark();
                readTerminalString(",");
                tokens.eraseMark();
            } catch (EPrimeSyntaxException e1) {
                tokens.reset();
                break;
            }
        }        // end of while loop

        readTerminalString(">");
        return CompoundMatrix.make(tupleContents);
    }

    /* ====================================================================
     readIdentifier()
     Rejects identifiers with leading digits (because read as a number).
     Should also reject reserved words like matrix. 
    ==================================================================== */

    private ASTNode readIdentifier() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read Identifier");
        }
        tokens.nextToken();
        if (tokens.tokenType != EPrimeTokenizer.TT_WORD || keywords.contains(tokens.wordToken)) {
            throw new EPrimeSyntaxException("Expected a variable identifier. Found: "+tokens.toString());
        }
        
        if (VB_MTDS) {
            System.out.println("succeeded to read Identifier " + tokens.wordToken);
        }
        return new Identifier(m, tokens.wordToken);
    }
    
    // Join some ranges into a finite domain. Make a shallow-ish tree.
    private ASTNode makeUnionOfRanges(ArrayList<ASTNode> ranges, int start, int end) {
        if (end - start < 5) {
            ASTNode union = new IntegerDomain(ranges.get(start));
            for (int i = start + 1; i < end; i++) {
                union = new Union(union, new IntegerDomain(ranges.get(i)));
            }
            return union;
        } else {
            return new Union(makeUnionOfRanges(ranges, start, start + (end - start) / 2), makeUnionOfRanges(ranges, start + (end - start) / 2, end));
        }
    }
    
    /* ====================================================================
     readUnboundedSetOfRanges()
     <UnboundedSetOfRanges> ::=
     (<Expression> ".." <Expression> | <Expression>) ["," <UnboundedSetOfRanges>]
    ==================================================================== */

    private ASTNode readUnboundedSetOfRanges() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read UnboundedSetOfRanges");
        }
        ArrayList<ASTNode> ranges = readRangeList();

        if (VB_MTDS) {
            System.out.println("UnboundedSetOfRanges read successfully");
        }

        return makeUnionOfRanges(ranges, 0, ranges.size());
    }
    
    //  Set parser.  {1,2,3}  or  { exp | ... } or {1..2, 3, 5..10}
    //  {} is an empty numerical set. 
    private ASTNode readSetComprehensionOrLiteral() throws EPrimeSyntaxException {
        readTerminalString("{");
        tokens.commit("Parsed '{' (start of set literal or set comprehension)");
        
        if(tryReadTerminalString("}")) {
            return new IntegerDomain(new EmptyRange());
        }
        boolean nocomma = false;
        
        ArrayList<ASTNode> l = new ArrayList<ASTNode>();
        while (true) {
            try {
                tokens.mark();
                ASTNode a = readExpression();
                tokens.eraseMark();
                
                if(tryReadTerminalString("..")) {
                    //  Read second half of range
                    tokens.commit("Read up to ..");
                    tokens.mark();
                    ASTNode b = readExpression();
                    tokens.eraseMark();
                    a=new Range(a,b);
                }
                
                l.add(a);
                if(l.size()==1) {
                    tokens.commit("Parsed first element in set literal or comprehension.");
                }
                else {
                    tokens.commit("Parsed element in set literal.");
                }
            } catch (EPrimeSyntaxException e2) {
                tokens.reset();
                break;
            }
            
            nocomma = ! tryReadTerminalString(",");
            if (nocomma) {
                break;
            }
            else {
                tokens.commit("Parsed ',' in set literal.");
            }
        }
        
        if (nocomma && l.size() == 1) {
            // Parsed one expression and then failed to parse a comma.
            // Test for |
            boolean bar = tryReadTerminalString("|");
            if (bar) {
                if(l.get(0) instanceof Range) {
                    throw new EPrimeSyntaxException("Expected a single expression in set comprehension, found an interval.");
                }
                tokens.commit("Parsed '|' (in set comprehension)");
                // Jump into set comprehension parser.
                return readSetComprehensionInner(l.get(0));
            }
        }
        
        readTerminalString("}");
        return makeUnionOfRanges(l, 0, l.size());
    }
    
    private ASTNode readSetComprehensionInner(ASTNode innerexp) throws EPrimeSyntaxException {
        // Read quantifiers.
        ArrayList<ASTNode> quantifiers = new ArrayList<ASTNode>();
        boolean first = true;
        while (true) {
            try {
                tokens.mark("cquant");
                if (!first) {
                    readTerminalString(",");
                }
                
                ASTNode ids = readIdList();
                
                readTerminalString(":");
                
                ASTNode domain = readExpression();
                
                tokens.eraseMark("cquant");
                for (int i =0; i < ids.numChildren(); i++) {
                    quantifiers.add(new ComprehensionForall(ids.getChild(i), domain));
                }
                first = false;
            } catch (EPrimeSyntaxException e2) {
                tokens.reset("cquant");
                break;
            }
        }
        
        // Now read conditions.
        ArrayList<ASTNode> conditions = new ArrayList<ASTNode>();
        while (true) {
            try {
                tokens.mark("ccond");
                if (!first) {
                    readTerminalString(",");
                }

                ASTNode condition = readExpression();

                tokens.eraseMark("ccond");
                conditions.add(condition);
                first = false;
            } catch (EPrimeSyntaxException e2) {
                tokens.reset("ccond");
                break;
            }
        }
        
        readTerminalString("}");
        return new ToSet(new ComprehensionMatrix(innerexp, quantifiers, new And(conditions)));
    }

    // Terminals %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    /* ====================================================================
     readConstant()
	 Either an Integer, or "true", or "false"
    ==================================================================== */
    private ASTNode readConstant() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("attempting to read constant");
        }
        try {
            tokens.mark();
            long a = readPositiveInt();
            tokens.eraseMark();
            return NumberConstant.make(a);
        } catch (EPrimeSyntaxException e1) {
            tokens.reset();
            try {
                tokens.mark();
                readTerminalString("true");
                tokens.eraseMark();
                return new BooleanConstant(true);
            } catch (EPrimeSyntaxException e2) {
                tokens.reset();
                readTerminalString("false");
                return new BooleanConstant(false);
            }
        }
        // if (VB_MTDS) System.out.println("constant read successfully") ;
    }
    
    ////////////////////////////////////////////////////////////////////////////
    //
    //   Basic methods for accessing tokens.
    
    /* ====================================================================
     readPositiveInt()
     Does not accept -5 -- this should be read as unaryminus 5. 
    ==================================================================== */
    
    private long readPositiveInt() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("Attempting to read Int");
        }
        tokens.nextToken();
        if (tokens.tokenType == EPrimeTokenizer.TT_INT) {
            return tokens.intToken;
        }
        
        throw new EPrimeSyntaxException("Expected positive integer.");
    }
    
    /* ====================================================================
     readTerminalString() and friends
    ==================================================================== */
    
    private boolean tryReadTerminalString(String t) {
        try {
            tokens.mark("trts");
            readTerminalString(t);
            tokens.eraseMark("trts");
            return true;
        } catch (EPrimeSyntaxException e1) {
            tokens.reset("trts");
            return false;
        }
    }
    
    private void readTerminalString(String terminal) throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("Attempting to read Terminal: " + terminal);
        }
        tokens.nextToken();
        if ((tokens.tokenType != EPrimeTokenizer.TT_WORD) && (tokens.tokenType != EPrimeTokenizer.TT_OTHER)) {
            throw new EPrimeSyntaxException("Expected "+terminal+", found "+tokens.toString());
        }
        if ((tokens.tokenType == EPrimeTokenizer.TT_WORD) && (!tokens.wordToken.equals(terminal))) {
            throw new EPrimeSyntaxException("Expected "+terminal+", found "+tokens.toString());
        }
        if ((tokens.tokenType == EPrimeTokenizer.TT_OTHER) && (!tokens.otherToken.equals(terminal))) {
            throw new EPrimeSyntaxException("Expected "+terminal+", found "+tokens.toString());
        }
        if (VB_MTDS) {
            System.out.println("Terminal read successfully");
        }
    }
    
    //  Read a given terminal string containing a prime character.
    private void readTerminalStringPrime(String terminal) throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("Attempting to read Terminal: " + terminal);
        }
        tokens.nextToken();
        if(tokens.tokenType != EPrimeTokenizer.TT_WORD_PRIME) {
            throw new EPrimeSyntaxException("Expected: "+terminal+" found: "+tokens.toString());
        }
        if( (tokens.tokenType == EPrimeTokenizer.TT_WORD_PRIME) && (!tokens.wordToken.equals(terminal))) {
            throw new EPrimeSyntaxException("Expected: "+terminal+" found: "+tokens.toString());
        }
        if (VB_MTDS) {
            System.out.println("Terminal read successfully");
        }
    }
    
    private String readTerminalString() throws EPrimeSyntaxException {
        if (VB_MTDS) {
            System.out.println("Attempting to read terminal string.");
        }
        tokens.nextToken();
        if ((tokens.tokenType == EPrimeTokenizer.TT_WORD)) {
            return tokens.wordToken;
        }
        if ((tokens.tokenType == EPrimeTokenizer.TT_OTHER)) {
            return tokens.otherToken;
        }
        throw new EPrimeSyntaxException("Unexpected:"+tokens.toString());
    }
    
    public class FunctionDescription {
        
        FunctionDescription(String nam, int arg) {
            className=nam;
            numArgs=arg;
        }
        
        public String className;
        public int numArgs;
        
        
        public ASTNode construct(ASTNode slot1, ASTNode slot2, ASTNode slot3, ASTNode slot4) {
            /*try {
                Class<?> t = Class.forName("savilerow."+className);
                Class<?> astnode=Class.forName("savilerow.ASTNode");
                
                if(numArgs==1) {
                    Constructor<?> c=t.getConstructor(astnode);
                    return (ASTNode) c.newInstance(slot1);
                }
                else if(numArgs==2) {
                    Constructor<?> c=t.getConstructor(astnode, astnode);
                    return (ASTNode) c.newInstance(slot1, slot2);
                }
                else if(numArgs==3) {
                    Constructor<?> c=t.getConstructor(astnode, astnode, astnode);
                    return (ASTNode) c.newInstance(slot1, slot2, slot3);
                }
                else if(numArgs==4) {
                    Constructor<?> c=t.getConstructor(astnode, astnode, astnode, astnode);
                    return (ASTNode) c.newInstance(slot1, slot2, slot3, slot4);
                }
                else {
                    CmdFlags.errorExit("At most 4 arguments allowed in generic function parser.");
                }
            }
            catch (Exception e) {
                CmdFlags.errorExit("Failed to construct function "+className+" with exception "+e);
            }*/
            
            //  Arity 1
            if(className.equals("ToSet")) {
                return new ToSet(slot1);
            }
            if(className.equals("Popcount")) {
                return new Popcount(slot1);
            }
            if(className.equals("ToInt")) {
                return new ToInt(slot1);
            }
            if(className.equals("MakeTable")) {
                return new MakeTable(slot1);
            }
            if(className.equals("IndexOf")) {
                return new IndexOf(slot1);
            }
            if(className.equals("Length")) {
                return new Length(slot1);
            }
            if(className.equals("AllDifferent")) {
                return new AllDifferent(slot1);
            }
            if(className.equals("Factorial")) {
                return new Factorial(slot1);
            }
            if(className.equals("TimesVector")) {
                return new TimesVector(slot1);
            }
            if(className.equals("AndVector")) {
                return new AndVector(slot1);
            }
            if(className.equals("OrVector")) {
                return new OrVector(slot1);
            }
            if(className.equals("XorVector")) {
                return new XorVector(slot1);
            }
            //  No SumVector because that must be parsed differently. 
            if(className.equals("Print")) {
                return new Print(slot1);
            }
            if(className.equals("IsRegularMatrix")) {
                return new IsRegularMatrix(slot1);
            }
            if(className.equals("FromSolution")) {
                return new FromSolution(slot1);
            }
            if(className.equals("DominanceRelation")) {
                return new DominanceRelation(slot1);
            }
            
            //  Arity 2
            if(className.equals("Count")) {
                return new Count(slot1, slot2);
            }
            if(className.equals("AllDifferentExcept")) {
                return new AllDifferentExcept(slot1, slot2);
            }
            if(className.equals("CatchUndef")) {
                return new CatchUndef(slot1, slot2);
            }
            if(className.equals("IncomparabilityFunction")) {
                return new IncomparabilityFunction(slot1, slot2);
            }
            if(className.equals("ElementId")) {
                return new ElementId(slot1, slot2);
            }
            
            //  Arity 3
            if(className.equals("AMOPB")) {
                return new AMOPB(slot1, slot2, slot3, true);
            }
            if(className.equals("EOPB")) {
                return new EOPB(slot1, slot2, slot3, true);
            }
            if(className.equals("GlobalCard")) {
                return new GlobalCard(slot1, slot2, slot3);
            }
            if(className.equals("AtMost")) {
                return new AtMost(slot1, slot2, slot3);
            }
            if(className.equals("AtLeast")) {
                return new AtLeast(slot1, slot2, slot3);
            }
            
            //  Arity 4
            if(className.equals("FrameUpdate")) {
                return new FrameUpdate(slot1, slot2, slot3, slot4);
            }
            if(className.equals("Cumulative")) {
                return new Cumulative(slot1, slot2, slot3, slot4);
            }
            
            CmdFlags.errorExit("Internal error constructing: "+className);
            return null;
        }
    }
}