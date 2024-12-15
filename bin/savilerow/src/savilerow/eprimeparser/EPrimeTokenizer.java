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




import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayDeque;

import savilerow.CmdFlags;
import savilerow.expression.Intpair;

public final class EPrimeTokenizer {
    private int ln;
    private char[] file;
    private int idx;
    private ArrayDeque<Integer> markStack;
    private ArrayDeque<String> markNames;
    private int commitMark;
    private String commitMsg;
    
    public int tokenType;
    public static final int TT_WORD = 0;
    public static final int TT_WORD_PRIME = 1;
    public static final int TT_OTHER = 2;
    public static final int TT_INT = 3;
    public static final int TT_EOF = 4;
    public String wordToken;
    public String otherToken;
    public long intToken;
    public String token;   //  Any token type stored here. 
    
    // Switches for verbose operation
    static final boolean VB_TOKENS = false;
    
    /* ====================================================================
     constructor()
    ==================================================================== */
    public EPrimeTokenizer(String fn, boolean isfilename) {
        if(isfilename) {
            // Treat fn as a file name
            File f = new File(fn);
            ln = (int) f.length();
            if (VB_TOKENS) {
                System.out.println("Reading " + fn + ", " + ln + " chars");
            }
            file = new char[ln];
            try {
                FileReader fr = new FileReader(fn);
                int numread = fr.read(file,0, ln);            // NOT WORKING PROPERLY IN GCJ
                
                /*   Use this code for GCJ:
                int numread=0;
                int tmp=fr.read();
                while(tmp!=-1) {
                    file[numread]=(char)tmp;
                    numread++;
                    tmp=fr.read();
                }*/
                
                fr.close();
            }
            catch (FileNotFoundException e) {
                CmdFlags.errorExit("File not found: "+fn);
            }
            catch (IOException e) {
                CmdFlags.errorExit("Unable to read file: "+fn); 
            }
        }
        else {
            // Treat fn as the E' to be parsed
            ln = fn.length();
            file = new char[ln];
            
            for (int i =0; i < ln; i++) {
                file[i] = fn.charAt(i);
            }
        }
        
        if (VB_TOKENS) {
            System.out.println(file);
        }
        idx = 0;
        markStack = new ArrayDeque<Integer>();
        markNames = new ArrayDeque<String>();
    }
    
    /* ====================================================================
     mark()
    ==================================================================== */
    public void mark() { markStack.push(Integer.valueOf(idx)); markNames.push("moo"); }

    public void mark(String nam) { markStack.push(Integer.valueOf(idx)); markNames.push(nam); }

    /* ====================================================================
     eraseMark()
    ==================================================================== */
    public void eraseMark() { markStack.pop(); String a = markNames.pop(); assert a.equals("moo"); }

    public void eraseMark(String nam) { markStack.pop(); String a = markNames.pop(); if (!nam.equals(a)) {
            System.out.println(nam + ", " + a);
        } assert nam.equals(a); }

    /* ====================================================================
     reset()
    ==================================================================== */
    public void reset() {
        idx = markStack.pop().intValue();
        if (idx < commitMark) {
            raiseError();
        }
        String a = markNames.pop();
        assert a.equals("moo");
    }

    public void reset(String nam) {
        idx = markStack.pop().intValue();
        if (idx < commitMark) {
            raiseError();
        }
        String a = markNames.pop();
        if (!nam.equals(a)) {
            System.out.println(nam + ", " + a);
        }
        assert nam.equals(a);
    }
    
    public void raiseError() {
        Intpair p = linecolNumber(commitMark);
        printMarker(p.lower, p.upper);
        if(commitMsg!=null) {
            CmdFlags.errorExit(commitMsg, "Failed when parsing rest of structure following line:" + p.lower + " column:" + p.upper);
        }
        else {
            CmdFlags.errorExit("Failed when parsing rest of structure following line:" + p.lower + " column:" + p.upper);
        }
    }
    
    /* ====================================================================
     commit()
     Commit the parser to never backtrack beyond this point.
    ==================================================================== */
    public void commit(String cMsg) { commitMark = idx; commitMsg = cMsg; }

    /* ====================================================================
     toString()
    ==================================================================== */
    public String toString() {
        switch (tokenType) {
            case TT_WORD: return "Token[" + wordToken + "]";
            case TT_INT: return "Token[" + intToken + "]";
            case TT_OTHER: return "Token[" + otherToken + "]";
            case TT_EOF: return "EOF";
            default: return "Unknown token type!!";
        }
    }

    /* ====================================================================
     lineNumber()
     Find the line and column numbers of the current position in the file.
    ==================================================================== */
    public Intpair linecolNumber(int filepos) {
        int line =1;
        for (int i =0; i < filepos; i++) {
            if (file[i] == '\n') {
                line++;
            }
        }

        int col =1;
        // really bad algorithm
        for (int i =0; i < filepos; i++) {
            col++;
            if (file[i] == '\n') {
                col = 0;
            }
        }

        return new Intpair(line, col);
    }

    public void printMarker(long lineerror, long columnerror) {
        int line =1;
        for (int i =0; i < file.length; i++) {
            if (line == lineerror) {
                System.err.print(file[i]);
            }
            if (file[i] == '\n') {
                line++;
            }
        }
        System.err.println("");
        for (int i =0; i < columnerror; i++) {
            System.err.print("-");
        }
        System.err.println("^");
    }


    /* ====================================================================
     nextToken()
     Ccould be word (identifier/keyword), number, or other (e.g. '{').
    ==================================================================== */
    public void nextToken() throws EPrimeSyntaxException {
        skipWS();
        
        if (tokenType == TT_EOF && idx >= ln - 1) {
            return;
        }
        char firstChar = file[idx];
        if ((('A' <= firstChar) && ('Z' >= firstChar)) || (('a' <= firstChar) && ('z' >= firstChar))) {
            nextWordToken();
        } else if (('0' <= firstChar) && ('9' >= firstChar)) {
            nextIntToken();
        } else {
            nextOtherToken();
        }
        skipWSaftertoken();   // Skip whitespace to improve parser error messages. 
    }
    
    /* ====================================================================
     nextWordToken()
     Assuming that the fact that this is a word has been checked (i.e. first 
     character is a-z or A-Z)
    ==================================================================== */
    private void nextWordToken() {
        StringBuilder result = new StringBuilder();
        boolean prime=false; // Does it contain a prime?
        for(; idx<ln && (
            ((file[idx] >= '0') && (file[idx] <= '9')) ||
            ((file[idx] >= 'A') && (file[idx] <= 'Z')) ||
            ((file[idx] >= 'a') && (file[idx] <= 'z')) ||
            (file[idx] == '_') ||
            (file[idx] == '\'') );
            idx++)
        {
            result.append(file[idx]);
            if(file[idx]=='\'') {
                prime=true;
            }
        }
        wordToken = result.toString();
        token=wordToken;
        if(!prime) {
            //  Conventional word
            tokenType = TT_WORD;
        }
        else {
            //  Special type of word that is allowed to contain '
            tokenType = TT_WORD_PRIME;
        }
        
        if (VB_TOKENS) {
            System.out.println(toString());
        }
    }
    
    /* ====================================================================
     nextIntToken()
     Assuming that the fact that this is an int has been checked.
     Also assumes that, if -ve, we have at least 2 chars.
    ==================================================================== */
    private void nextIntToken() {
        StringBuilder result = new StringBuilder();
        for(; idx<ln && (file[idx] >= '0') && (file[idx] <= '9'); idx++) {
            result.append(file[idx]);
        }
        try {
            token=result.toString();
            intToken = Long.parseLong(result.toString());
            tokenType = TT_INT;
            if (VB_TOKENS) {
                System.out.println(toString());
            }
        } catch (NumberFormatException e) {
            CmdFlags.errorExit("Number exceeds 64-bit integer range: "+result.toString());
        }
    }
    
    /* ====================================================================
     nextOtherToken()
     Can determine these singles immediately: , : ; [ ] ( ) { } * + - / |
     Need lookahead for these singles: < > .
     Can determine this double immediately: != ==
     These doubles have prefix common to singles: <= >= ..
    ==================================================================== */
    private void nextOtherToken() throws EPrimeSyntaxException {
        switch (file[idx++]) {
            case ',': otherToken = ","; break;
            case ':': otherToken = ":"; break;
            case ';': otherToken = ";"; break;
            case '[': otherToken = "["; break;
            case ']': otherToken = "]"; break;
            case '(': otherToken = "("; break;
            case ')': otherToken = ")"; break;
            case '{': otherToken = "{"; break;
            case '}': otherToken = "}"; break;
            case '@': otherToken = "@"; break;
            case '`': otherToken = "`"; break;
            case '*':
                if ((ln > idx) && (file[idx] == '*')) {
                    idx++;
                    otherToken = "**";
                } else {
                    otherToken = "*";
                }
                break;
            case '+': otherToken = "+"; break;
            case '-':
                if ((ln > idx) && (file[idx] == '>')) {
                    idx++;
                    otherToken = "->";
                } else {
                    otherToken = "-";
                }
                break;
            case '|': otherToken = "|"; break;
            case '%': otherToken = "%"; break;
            case '/':
                if ((ln > idx) && (file[idx] == '\\')) {
                    idx++;
                    otherToken = "/\\";
                } else {
                    otherToken = "/";
                }
                break;
            case '\\':
                if ((ln > idx) && (file[idx] == '/')) {
                    idx++;
                    otherToken = "\\/";
                    break;
                }
                throw new EPrimeSyntaxException("Expected OtherToken, found unknown token beginning with '\\'");
            case '.':
                if ((ln > idx) && (file[idx] == '.')) {
                    idx++;
                    otherToken = "..";
                } else {
                    otherToken = ".";
                }
                break;
            case '>':
                if ((ln > idx + 2) && (file[idx] == 'l') && (file[idx + 1] == 'e') && (file[idx + 2] == 'x')) {
                    idx = idx + 3;
                    otherToken = ">lex";
                } else if ((ln > idx + 3) && (file[idx] == '=') && (file[idx + 1] == 'l') && (file[idx + 2] == 'e') && (file[idx + 3] == 'x')) {
                    idx = idx + 4;
                    otherToken = ">=lex";
                } else if ((ln > idx) && (file[idx] == '=')) {
                    idx++;
                    otherToken = ">=";
                }
                else {
                    otherToken = ">";
                }
                break;
            case '<':
                if ((ln > idx + 2) && (file[idx] == 'l') && (file[idx + 1] == 'e') && (file[idx + 2] == 'x')) {
                    idx = idx + 3;
                    otherToken = "<lex";
                } else if ((ln > idx + 3) && (file[idx] == '=') && (file[idx + 1] == 'l') && (file[idx + 2] == 'e') && (file[idx + 3] == 'x')) {
                    idx = idx + 4;
                    otherToken = "<=lex";
                } else if ((ln > idx + 1) && (file[idx] == '=') && (file[idx + 1] == '>')) {
                    idx = idx + 2;
                    otherToken = "<=>";
                } else if ((ln > idx + 1) && (file[idx] == '-') && (file[idx + 1] == '>')) {
                    idx = idx + 2;
                    otherToken = "<->";
                } else if ((ln > idx) && (file[idx] == '=')) {
                    idx++;
                    otherToken = "<=";
                } else {
                    otherToken = "<";
                }
                break;
            case '!':
                if ((ln > idx) && (file[idx] == '=')) {
                    idx++;
                    otherToken = "!=";
                    break;
                } else {
                    otherToken = "!";
                }
                break;
            case '=':
                if ((ln > idx) && (file[idx] == '>')) {
                    idx++;
                    otherToken = "=>";
                    break;
                }
                otherToken = "=";
                break;
            default:
                throw new EPrimeSyntaxException("Expected OtherToken, found unknown token beginning with " + Character.toString(file[idx - 1]));
        }
        tokenType = TT_OTHER;
        token=otherToken;
        if (VB_TOKENS) {
            System.out.println(toString());
        }
        return;
    }

    /* ====================================================================
     skipWS()
     When done, idx points to the first character of non whitespace.
     Ignores comment lines (comment character: "$"
     Detects and flags EOF. Copes with case where already at EOF when called.
    ==================================================================== */
    private void skipWS() {
        boolean commentLine = false;
        while (idx < ln) {
            if (commentLine) {
                if ((file[idx] == '\n') || (file[idx] == '\r')) {
                    commentLine = false;
                }
                idx++;
            } else {
                if (file[idx] == '$') {
                    commentLine = true;
                } else if (file[idx] > ' ') {
                    return;
                }
                idx++;
            }
        }
        tokenType = TT_EOF;
        token="";
    }
    
    // Does not set EOF token type because this is called at the end of nextToken.
    private void skipWSaftertoken() {
        boolean commentLine = false;
        while (idx < ln) {
            if (commentLine) {
                if ((file[idx] == '\n') || (file[idx] == '\r')) {
                    commentLine = false;
                }
                idx++;
            } else {
                if (file[idx] == '$') {
                    commentLine = true;
                } else if (file[idx] > ' ') {
                    return;
                }
                idx++;
            }
        }
    }
}