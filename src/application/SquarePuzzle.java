/**
 *  SquarePuzzle.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *  Copyright (C) 2014 Ismail AKBUDAK
 *
 */

package application;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Pattern;

import  org.jacop.constraints.Alldistinct;
import  org.jacop.constraints.Sum;
import  org.jacop.constraints.SumWeight;
import  org.jacop.constraints.XneqC;
import  org.jacop.core.IntDomain;
import  org.jacop.core.IntVar;
import  org.jacop.core.Store;
import  org.jacop.core.Var;
import core.Base;

/**
 * SquarePuzzle. It solves any cryptogram puzzle of the form like SEND+MORE=MONEY.
 *
 * @author  Ismail AKBUDAK
 */

public class SquarePuzzle extends Base {

	/**
	 * It specifies how many lines of expressions can be inputed in one
	 * execution.
	 */
	public int maxInputLines = 100;

	/**
	 * It specifies the base of the numerical system to be used in the calculations.
	 */
	public int base = 10;

	/**
	 * It specifies the file which contains the puzzle to be solved.
	 */
	public String filename;
	
	private static int[] createWeights(int length, int base) {

		int[] weights = new int[length];

		weights[length - 1] = 1;

		for (int i = length - 2; i >= 0; i--)
			weights[i] = weights[i + 1] * base;

		return weights;
	}

	
	@Override
	public void model() {

		String lines[] = new String[maxInputLines];

		// Standard use case if no file is supplied		
		// lines[0] = "SEND+MORE=MONEY";
		// lines[0] = "BASIC+LOGIC=PASCAL";
		// lines[0] = "CRACK+HACK=ERROR";
		// lines[0] = "PEAR+APPLE=GRAPE";
	 	// lines[0] = "CRACKS+TRACKS=RACKET";
	 	// lines[0] = "TRIED+RIDE=STEER";
	 	// lines[0] = "DEEMED+SENSE=SYSTEM";
                // lines[0] = "DOWN+WWW=ERROR";
                // lines[0] = "BARREL+BROOMS=SHOVELS";
                // lines[0] = "LYNNE+LOOKS=SLEEPY";
                // lines[0] = "STARS+RATE=TREAT";
                // lines[0] = "DAYS+TOO=SHORT";
                // lines[0] = "BASE+BALL=GAMES";
                // lines[0] = "MEMO+FROM=HOMER";
                 lines[0] =  "IS+THIS=HERE";
                // lines[0] = "HERE+SHE=COMES";
	 	
		int noLines = 1;

		if (filename != null) {

			/* read from file args[0] */
			try {

				BufferedReader in = new BufferedReader(new FileReader(filename));
				String str;

				while ((str = in.readLine()) != null)
					if (!str.trim().equals("")) {

						int commentPosition = str.indexOf("//");
						if (commentPosition == 0)
							continue;
						else
							str = str.substring(0, commentPosition);

						lines[noLines] = str;
						noLines++;

					}
				in.close();
			} catch (FileNotFoundException e) {
				System.err.println("File " + filename + " could not be found");
			} catch (IOException e) {
				System.err.println("Something is wrong with the file"
						+ filename);
			}
		} else {
			System.out.println("No input file was supplied, using standard HERE+SHE=COMES problem");
		}

		/* Creating constraint store */
		store = new Store();

		ArrayList<ArrayList<String>> words = new ArrayList<ArrayList<String>>();

		// Adding array list for each inputed line
		for (int i = 0; i < noLines; i++)
			words.add(new ArrayList<String>());

		// letters used in the file.
		HashMap<String, IntVar> letters = new HashMap<String, IntVar>();

		// parsing the words within each line.
		for (int i = 0; i < noLines; i++) {
			Pattern pat = Pattern.compile("[=+]");
			String[] result = pat.split(lines[i]);

			for (int j = 0; j < result.length; j++)
				words.get(i).add(result[j]);
		}

		vars = new ArrayList<Var>();

		for (int i = 0; i < noLines; i++)
			for (int j = words.get(i).size() - 1; j >= 0; j--)
				for (int z = words.get(i).get(j).length() - 1; z >= 0; z--) {
					char[] currentChar = { words.get(i).get(j).charAt(z) };
					if (letters.get(new String(currentChar)) == null) {
						IntVar currentLetter = new IntVar(store, new String(
								currentChar), 0, base - 1);
						vars.add(currentLetter);
						letters.put(new String(currentChar), currentLetter);
					}
				}

		if (letters.size() > base) {
			System.out.println("Expressions contain more than letters than base of the number system used ");
			System.out.println("Base " + base);
			System.out.println("Letters " + letters);
			System.out.println("There can not be any solution");
		}

		store.impose(new Alldistinct(vars.toArray(new IntVar[0])));

		for (int currentLine = 0; currentLine < noLines; currentLine++) {

			int noWords = words.get(currentLine).size();

			IntVar[] fdv4words = new IntVar[noWords];
			IntVar[] terms = new IntVar[noWords - 1];

			for (int j = 0; j < noWords; j++) {

				String currentWord = words.get(currentLine).get(j);
				fdv4words[j] = new IntVar(store, currentWord, 0, IntDomain.MaxInt);

				// stores fdvs corresponding to all but the last one in the
				// separate
				// array for later use.
				if (j < noWords - 1)
					terms[j] = fdv4words[j];

				IntVar[] lettersWithinCurrentWord = new IntVar[currentWord.length()];

				for (int i = 0; i < currentWord.length(); i++) {
					char[] currentChar = { currentWord.charAt(i) };
					lettersWithinCurrentWord[i] = letters.get(new String(
							currentChar));
				}

				store.impose(new SumWeight(lettersWithinCurrentWord,
								createWeights(currentWord.length(), base),
								fdv4words[j]));

				store.impose(new XneqC(lettersWithinCurrentWord[0], 0));

			}

			store.impose(new Sum(terms, fdv4words[noWords - 1]));
		}

	}
		
	/**
	 * It executes the program to solve any cryptographic puzzle.
	 * @param args no arguments read.
	 */
	public static void main(String args[]) {

		SquarePuzzle example = new SquarePuzzle();
		
		example.model();

		if (example.searchMostConstrainedStatic())
			System.out.println("\nSolution(s) found");
	}			
	
	
}
