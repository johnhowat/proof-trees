/*
** COMP 4905 - Honours Project
** School of Computer Science, Carleton University
** Fall 2006
**
** Proof Trees for Propositional Logic with Extensions to First Order Logic
**
** John Howat
** jhowat@primus.ca
*/

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.InputStreamReader;
import java.io.IOException;
import java.util.Vector;

/**
 * The <code>prove</code> class functions as the entry point into the program.
 * The user must enter his or her argument in one of two ways.
 * <p>
 * The user may elect to supply a file containing the argument. To do this, the
 * user passes the filename on the command line. The file should list one
 * premise per line followed by the conclusion on the last line. Blank lines
 * are allowed. The conclusion of the argument should be the actual conclusion,
 * i.e., unnegated.
 * <p>
 * Alternatively, the user may wish to input the argument manually. To do this,
 * the user must pass no arguments on the command line. The user will be
 * prompted to enter premises, one per line, followed by <code>Enter</code>.
 * After all premises have been entered, a blank premise should be entered. The
 * conclusion will then be entered, again followed by <code>Enter</code>. As
 * before, the conclusion of the argument should be the actual conclusion, i.e.,
 * unnegated.
 * <p>
 * The program will proceed to build a proof tree. Once built (if the algorithm
 * terminates) the user will be presented with the building time, the size of
 * the tree, the validity of the argument and the tree itself.
 */
public class prove {
	/**
	 * The source of the input for the program.
	 */
	private static BufferedReader input;

	/**
	 * Reads and returns a line from the input.
	 * 
	 * @return a string consisting of the next line of input
	 * @throws IOException if an I/O error occurs
	 */
	private static String readLine() throws IOException {
		return(input.readLine());
	}

	/**
	 * Reads in an argument from input without prompts (i.e., from a file.) The
	 * caller must split the returned formulae into premises and a conclusion.
	 *
	 * @return a list of formulae returned from the input
	 * @throws IOException if an I/O error occurs
	 */
	private static Vector<Formula> getArgumentFromFile() throws IOException {
		Vector<Formula> formulae = new Vector<Formula>();
		String line;
		while((line = readLine()) != null) {
			if(!line.equals("")) {	
				formulae.add(new Formula(line));
			}
		}
		return(formulae);
	}

	/**
	 * Reads in an argument from input with prompts (i.e., from the console.)
	 * The caller must split the returned formulae into premises and a
	 * conclusion.
	 *
	 * @return a list of formulae returned from the input
	 * @throws IOException if an I/O error occurs
	 */
	private static Vector<Formula> getArgumentFromConsole() throws IOException {
		Vector<Formula> formulae = new Vector<Formula>();
		System.out.println("Please enter each premise followed by Enter.");
		System.out.println("Enter a blank premise when done.");

		while(true) {
			System.out.print("Premise " + (formulae.size() + 1) + ": ");
			String line = readLine();
			if(line.equals("")) {
				break;
			} else {
				Formula f;
				try {
					f = new Formula(line);
				} catch(Exception e) {
					System.out.println("Poorly formed premise! Please re-enter.");
					continue;	
				}
				formulae.add(f);
			}
		}

		while(true) {
			System.out.print("Conclusion: ");
			String line = readLine();
			Formula f;
			try {
				f = new Formula(line);
			} catch(Exception e) {
				System.out.println("Poorly formed conclusion! Please re-enter.");
				continue;	
			}
			formulae.add(f);
			break;
		}

		return(formulae);
	}

	/**
	 * Reads in an argument, builds a proof tree, and reports information about
	 * the specified argument. This is the main entry point for the program.
	 */
	public static void main(String[] args) {
		Vector<Formula> premises = null;
		try {
			if(args.length == 1) {
				String filename = "";
				for(int i = 0; i < args.length; i++) {
					filename += args[i];
					if(i < args.length - 1) {
						filename += " ";
					}
				}
				input = new BufferedReader(new FileReader(filename));
				premises = getArgumentFromFile();
			} else {
				input = new BufferedReader(new InputStreamReader(System.in));
				premises = getArgumentFromConsole();
			}
		} catch(Exception e) {
			System.err.println("Error: " + e.getMessage());
			System.exit(1);
		}
		Formula conclusion = premises.remove(premises.size() - 1);

		long start = System.nanoTime();
		ProofTree tree = ProofTreeGenerator.generateProofTree(premises, conclusion);
		long stop = System.nanoTime();

		System.out.println("Tree build time: " + ((double)(stop-start)/1000000000.0) + " seconds");
		System.out.println("Tree size      : " + tree.size());
		System.out.println("Argument type  : " + (tree.closes() ? "valid" : "invalid"));
		System.out.println();
		System.out.print(tree);
	}
}