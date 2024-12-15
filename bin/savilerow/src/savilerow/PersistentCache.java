package savilerow;
/*

    Savile Row http://savilerow.cs.st-andrews.ac.uk/
    Copyright (C) 2014-2024 Christopher Jefferson
    
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

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.math.BigInteger;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

public class PersistentCache {

    static File basedir = new File(System.getProperty("user.home") + "/.savilerow/tablecache/" + RepositoryVersion.repositoryVersion);

    public PersistentCache() {
        if(!basedir.exists()) {
            boolean create = basedir.mkdirs();
            if(!create) {
                CmdFlags.errorExit("Unable to create table cache");
            }
        }
    }
    
    
    public static String getHash(String name) {
            try {
                MessageDigest messageDigest = MessageDigest.getInstance("SHA-256");
                messageDigest.update(name.getBytes());
                return new BigInteger(1, messageDigest.digest()).toString(16);
            }
            catch(NoSuchAlgorithmException e)
            {
                CmdFlags.errorExit("SHA-256 doesn't exist");
            }
            return null;
    }
    
    public void addToCache(String name, String input) {
        CmdFlags.printlnIfVerbose("adding to cache");
        File filename = new File(basedir, getHash(name));
        try(PrintWriter out = new PrintWriter(filename)) {
            out.print("# ");
            out.println(name);
            out.println(input);
        }
        catch(FileNotFoundException e) {
            CmdFlags.errorExit("Unable to write cache file: " + filename);
        }
    }
    
    public String findInCache(String name) {
        File filename = new File(basedir, getHash(name));
        if(!filename.exists()) {
            CmdFlags.printlnIfVerbose("Cache miss");
            return null;
        }
        else {
            CmdFlags.printlnIfVerbose("Cache hit");
            try {
                BufferedReader brTest = new BufferedReader(new FileReader(filename));
                String firstLine = brTest.readLine();
                if(!firstLine.equals("# " + name)) {
                    System.out.println("ERROR: Cache hash collision");
                    System.out.println(filename);
                    System.out.println("E: '# " + name + "'");
                    System.out.println("G: '" + firstLine +"'");
                    CmdFlags.exit();
                }
                StringBuilder otherLines = new StringBuilder();
                String line;
                while( (line = brTest.readLine()) != null) {
            otherLines.append(line);
            }
                brTest.close();
            return otherLines.toString();
            }
            catch(IOException io) {
                CmdFlags.errorExit("Unable to read cache file");
            }
        }
        return null; // should never be reached
    }

}
