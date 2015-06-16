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

import java.util.Stack;
import java.util.StringTokenizer;
import java.util.Vector;

/**
 * The <code>Formula</code> class represents formulae in first-order logic
 * Since propositional logic is a subset of first-order logic, this class also
 * represents formulae in propositional logic.
 * 
 * @author John Howat
 */
public class Formula {
	/**
	 * The symbol used for negation.
	 */
	public static final String NEGATION = "~";

	/**
	 * The symbol used for disjunction.
	 */
	public static final String DISJUNCTION = "+";

	/**
	 * The symbol used for conjunction.
	 */
	public static final String CONJUNCTION = "&";

	/**
	 * The symbol used for if-then.
	 */
	public static final String IFTHEN = ">";

	/**
	 * The symbol used for if and only if (iff).
	 */
	public static final String IFF = ":";

	/**
	 * The symbol used for universal quantification.
	 */
	public static final String FORALL = "@";

	/**
	 * The symbol used for existential quantification.
	 */
	public static final String EXISTS = "#";

	/**
	 * The symbol used for an opening bracket.
	 */
	public static final String OPEN_BRACKET = "(";

	/**
	 * The symbol used for a closing bracket.
	 */
	public static final String CLOSE_BRACKET = ")";

	/**
	 * A string consisting of all possible brackets. Used for testing to see
	 * if something is itself a bracket.
	 */
	private static final String BRACKETS = OPEN_BRACKET + CLOSE_BRACKET;

	/**
	 * A string consisting of all possible operators. Used for testing to see
	 * if something is itself an operator.
	 */
	private static final String OPERATORS = NEGATION + DISJUNCTION + CONJUNCTION + IFTHEN + IFF;

	/**
	 * A string consisting of all possible quantifiers. Used for testing to see
	 * if something is itself a quantifier.
	 */
	private static final String QUANTIFIERS = FORALL + EXISTS;

	/**
	 * A string consisting of all possible predicates. Used for testing to see
	 * if something is itself a predicate.
	 */
	private static final String PREDICATES = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";

	/**
	 * A string consisting of all possible delimiters. Used for testing to see
	 * if something is itself a delimiter.
	 */
	private static final String DELIMITERS = OPERATORS + QUANTIFIERS + OPEN_BRACKET + CLOSE_BRACKET + PREDICATES;

	/**
	 * A representation of this formula, stored in prefix (Polish) notation.
	 */
	private String[] formula;

	/**
	 * Creates a new <code>Formula</code> from the given representation. The
	 * representation will be stored in prefix (Polish) notation, but can be
	 * specified to the constructor in either infix or prefix notation.
	 *
	 * @param formula a formula of first-order logic, in either infix or
	 * 	prefix notation.
	 * @throws IllegalArgumentException if the formula is not well-formed
	 */
	public Formula(String formula) {
		String[] tokens = tokenize(formula);
		if(!isValidPrefixNotation(tokens)) {
			tokens = toPrefixNotation(tokens);
			if(!isValidPrefixNotation(tokens)) {
				throw new IllegalArgumentException(toString(tokens) + " is not a well formed formula");
			} else {
				this.formula = tokens;
			}
		} else {
			this.formula = tokens;
		}
	}

	/**
	 * Creates a new <code>Formula</code> from the given array of formula
	 * tokens. The tokens can be specified in either infix or prefix notation,
	 * but will be converted into prefix notation upon construction.
	 * 
	 * @param tokens an array of formula tokens
	 * @throws IllegalArgumentException if the formula is not well-formed
	 */
	private Formula(String[] tokens) {
		if(!isValidPrefixNotation(tokens)) {
			tokens = toPrefixNotation(tokens);
			if(!isValidPrefixNotation(tokens)) {
				throw new IllegalArgumentException(toString(tokens) + " is not a well formed formula");
			} else {
				this.formula = tokens;
			}
		} else {
			this.formula = tokens;
		}
	}

	/**
	 * Returns the negation of this formula.
	 *
	 * @return the negation of this formula
	 */
	public Formula getNegation() {
		String[] tokens = new String[this.formula.length + 1];
		tokens[0] = NEGATION;
		for(int i = 0; i < this.formula.length; i++) {
			tokens[i + 1] = this.formula[i];
		}
		return(new Formula(tokens));
	}

	/**
	 * Returns the major operator of this formula. The major operator is defined
	 * as the operator which would be evaluated last; it separates the largest
	 * possible subformulae.
	 *
	 * @return the major operator of this formula
	 * @see #OPERATORS
	 */
	public String getMajorOperator() {
		return((this.formula.length > 1) ? this.formula[0] : "");
	}

	/**
	 * Returns a <code>Vector</code> containing the major operand(s) of this
	 * formula. The major operand(s) are the operand(s) of the major operator of
	 * the formula.
	 *
	 * @return a <code>Vector</code> containing the major operand(s) of this
	 *  formula
	 * @see #getMajorOperator()
	 */
	public Vector<Formula> getMajorOperands() {
		Vector<Formula> result = new Vector<Formula>();
		if(this.getMajorOperator().equals(NEGATION) || this.getMajorOperator().startsWith(EXISTS) || this.getMajorOperator().startsWith(FORALL)) {
			result.add(new Formula(getRange(this.formula, 1, this.formula.length)));
		} else if(this.formula.length == 1) {
			result.add(this);
		} else {
			String[] subformula = getRange(this.formula, 1, this.formula.length);
			int needed = 1;
			int i;
			for(i = 0; i < subformula.length; i++) {
				String token = subformula[i];
				if((DISJUNCTION + CONJUNCTION + IFTHEN + IFF).contains(token)) {
					needed += 1;
				} else if(token.equals(NEGATION) || token.startsWith(EXISTS) || token.startsWith(FORALL)) {
					needed += 0;
				} else {
					needed -= 1;
				}
				if(needed == 0) {
					break;
				}
			}
			result.add(new Formula(getRange(subformula, 0, i + 1)));
			result.add(new Formula(getRange(subformula, i + 1, subformula.length)));
		}
		return(result);
	}

	/**
	 * Returns a <code>Vector</code> containing all of the non-bound terms in
	 * this formula.
	 *
	 * @return a <code>Vector</code> containing all of the non-bound terms in
	 * this formula
	 */
	public Vector<String> getConstants() {
		return(getConstants(this, new Vector<String>()));
	}

	/**
	 * Returns a <code>Vector</code> containing all of the non-bound variables
	 * within the given subformula. Duplicates will not be included.
	 *
	 * @param f a <code>Formula</code> to be examined for non-bounded variables
	 * @param bound a <code>Vector</code> containing terms that have been
	 *  previously bound (i.e., in a previous call, higher in the recursion
	 *  tree.)
	 * @return a <code>Vector</code> containing all of the non-bound terms in
	 *  the given subformula
	 * @see #getConstants()
	 */
	private static Vector<String> getConstants(Formula f, Vector<String> bound) {
		Vector<String> result = new Vector<String>();
		String operator = f.getMajorOperator();
		if(operator.equals("")) {
			for(int i = 0; i < f.formula[0].length(); i++) {
				String current = f.formula[0].substring(i, i + 1);
				if(current.toLowerCase().equals(current) && !bound.contains(current)) {
					result.add(current);
				}
			}
		} else {
			if(operator.startsWith(FORALL) || operator.startsWith(EXISTS)) {
				bound.add(operator.substring(1));
			}
			if(!operator.equals("")) {
				for(int i = 0; i < f.getMajorOperands().size(); i++) {
					Vector<String> others = getConstants(f.getMajorOperands().get(i), new Vector<String>(bound));
					for(int j = 0; j < others.size(); j++) {
						if(!result.contains(others.get(j))) {
							result.add(others.get(j));
						}
					}
				}
			}
		}
		return(result);
	}

	/**
	 * Returns a copy of this formula with all occurences of the given variable
	 * replaced by the given constant. It is the responsibility of the caller
	 * to ensure that the substitution is semantically legal, i.e., that only
	 * bound occurences are replaced.
	 *
	 * @param variable the variable to be replaced
	 * @param constant the constant to substitute in the variable's place
	 * @return a new <code>Formula</code> with this substitution
	 */
	public Formula substitute(String variable, String constant) {
		return(new Formula(toString(this.formula).replaceAll(variable, constant)));
	}

	/**
	 * Answers whether or not this formula is an atom. A formula is an atom if
	 * it is either a literal or a negation of a literal.
	 *
	 * @return <code>true</code> if the specified Formula is an atom;
	 *  <code>false</code> otherwise
	 */
	public boolean isAtom() {
		return(
			toString(this.formula).matches("^[" + NEGATION + PREDICATES + PREDICATES.toLowerCase() + "]+$")
		);
	}

	/**
	 * Answers whether or not a given formula contradicts this one. Only atoms
	 * may contradict one another.
	 *
	 * @param formula a formula to be tested for contradiction with this one
	 * @return <code>true</code> if the specified formula contradicts this one
	 * 	provided that they are both atoms; <code>false</code> otherwise
	 * @see #isAtom()
	 */
	public boolean contradicts(Formula formula) { 
		return(
			(this.isAtom() && formula.isAtom()) && 
			(formula.getNegation().equals(this) ||
			this.getNegation().equals(formula))
		);
	}

	/**
	 * Answers whether or not this <code>Formula</code> is equal to another
	 * object. A necessary condition for an object being equal to a <code>
	 * Formula</code> is that the object is an instance of <code>Formula</code>.
	 * Beyond this, two formulae are equal if and only if their string
	 * representations are equal.
	 *
	 * @param obj the <code>Object</code> to be tested for equality
	 * @return <code>true</code> if the specified object is equal to this
	 *	<code>Formula</code>; <code>false</code> otherwise
	 */
	public boolean equals(Object obj) {
		if(!(obj instanceof Formula)) {
			return(false);
		} else {
			Formula other = (Formula)obj;
			for(int i = 0; i < Math.min(other.formula.length, this.formula.length); i++) {
				if(!other.formula[i].equals(this.formula[i])) {	
					return(false);
				}
			}
			return(other.formula.length == this.formula.length);
		}
	}

	/**
	 * Returns a string representation of this formula in prefix notation.
	 *
	 * @return a String representation of this formula
	 */
	public String toString() {
		return(toString(this.formula));
	}

	/**
	 * Tokenizes the given string representation of a formula into an array of
	 * tokens. The notation (i.e., infix of prefix) is the same as the original
	 * string.
	 *
	 * @param formula a string representation of the formula to be tokenized
	 * @return an array of tokens representing the given formula
	 */
	private String[] tokenize(String formula) {
		formula = formula.replaceAll("\\s+", "");
		Vector<String> result = new Vector<String>();
		StringTokenizer tokens = new StringTokenizer(formula, DELIMITERS, true);
		while(tokens.hasMoreTokens()) {
			String token = tokens.nextToken().trim();
			if(OPERATORS.contains(token) || BRACKETS.contains(token)) {
				result.add(token);
			} else if(tokens.hasMoreTokens()) {
				String next = tokens.nextToken().trim();
				if(DELIMITERS.contains(next.substring(0, 1))) {
					result.add(token);
					result.add(next);
				} else {
					result.add(token + next);
				}
			} else {
				result.add(token);
			}
		}
		return(result.toArray(new String[0]));
	}

	/**
	 * Converts the given array of tokens representing a formula into prefix
	 * (Polish) notation. No attempt is made to verify the result is
	 * well-formed, although this is guaranteed if the input was well-formed.
	 *
	 * @param formula an array of tokens representing a formula in infix
	 *  notation
	 * @return an array of tokens representating the given formula in prefix
	 *  notation
	 * @see http://www.calstatela.edu/faculty/jguo/teaching/cs490/InfixPrefixAndPostfix.ppt
	 */
	private static String[] toPrefixNotation(String[] formula) {
		Stack<String> stack = new Stack<String>();
		Vector<String> result = new Vector<String>();

		for(int i = formula.length - 1; i >= 0; i--) {
			String token = formula[i];
			if(OPERATORS.contains(token.substring(0, 1))) {
				boolean repeat = true;
				while(repeat) {
					repeat = false;
					if(
						stack.empty() ||
						stack.peek().equals(CLOSE_BRACKET) ||
						(operatorPriority(stack.peek()) >= operatorPriority(token))
					) {
						stack.push(token);
					} else {
						result.add(0, stack.pop());
						repeat = true;
					}
				}
			} else if(token.equals(OPEN_BRACKET)) {
				String top;
				while(!(top = stack.pop()).equals(CLOSE_BRACKET)) {
					result.add(0, top);
				}
			} else if(token.equals(CLOSE_BRACKET)) {
				stack.push(token);
			} else {
				result.add(0, token);
			}
		}
		while(!stack.empty()) {
			result.add(0, stack.pop());
		}

		return(result.toArray(new String[0]));
	}

	/**
	 * Answers whether or not the given string representation of a formula in
	 * prefix notation is valid, i.e., well-formed.
	 *
	 * @param formula a formula in prefix notation to be checked for validity
	 * @return <code>true</code> if the given formula is well-formed;
	 * 	<code>false</code> otherwise
	 */
	private static boolean isValidPrefixNotation(String[] formula) {
		String current = toString(formula);
		String original = "";
		while(!original.equals(current)) {
			original = current;
			current = current.replaceAll("[" + FORALL + EXISTS + "][^" + DELIMITERS + "]", "");
			current = current.replaceAll("[A-Z][a-z]*", "t");
			current = current.replaceAll("[" + CONJUNCTION + DISJUNCTION + IFTHEN + IFF + "][^" + OPERATORS + "]{2}","t");
			current = current.replaceAll(NEGATION + "[^" + OPERATORS + "]", "t");
			
		}
		return((current.length() == 1) && (!DELIMITERS.contains(current)));
	}

	/**
	 * Gives the priority of the operator. The smaller the number, the more
	 * tightly the operator binds. The intent of this method is to compare the
	 * priority of two operators; the integer returned is meaningless on its
	 * own.
	 *
	 * @param operator the operator whose priority is to be determined
	 * @return an integer representing the priority of the given operator
	 * @see #OPERATORS
	 */
	private static int operatorPriority(String operator) {
		if(operator.equals(NEGATION)) {
			return(1);
		} else if(operator.startsWith(FORALL)) {
			return(2);
		} else if(operator.startsWith(EXISTS)) {
			return(2);
		}  else if(operator.equals(CONJUNCTION)) {
			return(3);
		} else if(operator.equals(DISJUNCTION)) {
			return(4);
		} else if(operator.equals(IFTHEN)) {
			return(5);
		} else if(operator.equals(IFF)) {
			return(6);
		} else {
			return(0);
		}
	}

	/**
	 * Converts an array of tokens into a string representation.
	 *
	 * @param s the array of tokens to be converted to a string representation
	 * @return a string representation of the given array of tokens
	 */
	private static String toString(String[] s) {
		String result = "";
		for(int i = 0; i < s.length; i++) {
			result += s[i];
		}
		return(result);
	}

	/**
	 * Returns a subrange of the given array of tokens.
	 *
	 * @param original the array of tokens to be examined
	 * @param begin the index to start copying from, inclusive
	 * @param end the index to copy until, exclusive
	 * @return the specified subrange of the given array
	 */
	private static String[] getRange(String[] original, int begin, int end) {
		String[] result = new String[end - begin];
		for(int i = begin; i < end; i++) {
			result[i - begin] = original[i];
		}
		return(result);
	}
}