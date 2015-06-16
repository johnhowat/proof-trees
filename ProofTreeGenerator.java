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

import java.util.Iterator;
import java.util.Vector;

/**
 * The <code>ProofTreeGenerator</code> class generates a proof tree. Proof trees
 * themselves are described in detail the accompanying paper. Essentially, proof
 * trees are trees representing derivations of proofs for (in this case) first
 * order logic. The tree is built by applying various tree rules. These rules
 * can be applied in different orders, and the goal of this class is to apply
 * them in such a way as to minimize proof tree size as much as possible.
 * Additionally, since first order logic is undecidable, some proof trees may
 * not have finite length, i.e., the generation algorithm may not terminate. The
 * heuristics used to apply the rules try to avoid this, but they cannot do
 * this in all cases.
 */
public class ProofTreeGenerator {
	/**
	 * Generate a proof tree for the given argument.
	 *
	 * @param premises a list of the premises of the argument
	 * @param conclusion the (unnegated) conclusion of the argument.
	 * @return a <code>ProofTree</code> object representing a proof tree for
	 *  this argument (although termination is not guaranteed)
	 */
	public static ProofTree generateProofTree(Vector<Formula> premises, Formula conclusion) {
		ProofTree tree = generateInitialTree(premises, conclusion);

		if(tree.checkContradictionFrom(tree.getRoot())) {
			tree.getRoot().close();
			return(tree);
		}

		Vector<Condition> preferences = new Vector<Condition>();
		preferences.add(getMakesContradictionCondition());
		preferences.add(getQuantifierNegationCondition());
		preferences.add(getNonBranchingSententialCondition());
		preferences.add(getExistentialInstantiationCondition());
		preferences.add(getUniversalInstantiationCondition());
		preferences.add(getBranchingSententialCondition());
		preferences.add(getWildCardCondition());

		applyRulesWithPreferences(tree, preferences);
		return(tree);
	}

	/**
	 * Generate an initial tree for the given argument.
	 * 
	 * @param premises a list of the premises of the argument
	 * @param conclusion the (unnegated) conclusion of the argument.
	 * @return a <code>ProofTree</code> object representing an initial proof
	 * proof tree for the argument
	 */
	private static ProofTree generateInitialTree(Vector<Formula> premises, Formula conclusion) {
		Vector<Formula> rootFormulae = new Vector<Formula>();
		rootFormulae.addAll(premises);
		rootFormulae.add(conclusion.getNegation());
		return(new ProofTree(new ProofTreeNode(rootFormulae)));
	}

	/**
	 * Apply the tree rules using the given preferences. Preferences describe
	 * the order in which rule should be applied. The method tries to apply the
	 * preferences in the order they are specified until a change is made, and
	 * then goes back to the beginning to try to apply the next rule. Therefore,
	 * the most preferred rule is always applied at any given stage.
	 *
	 * @param tree the tree to which the tree rules are to be applied
	 * @param preferences a list of preferences, in the order in which they are
	 *  to be applied
	 */
	private static void applyRulesWithPreferences(ProofTree tree, Vector<Condition> preferences) {
		for(int i = 0; i < preferences.size(); i++) {
			if(applyRuleToTreeWhere(tree, preferences.get(i))) {
				i = -1;
			}
		}
	}

	/**
	 * Attempt to apply a tree rule given using the given preference, i.e., if
	 * the preference is satisified by any application of a rule, then apply it.
	 *
	 * @param tree the tree to which the tree rule is to be applied
	 * @param condition the preference currently under consideration
	 * @return <code>true</code> if the condition was satisfied and the tree
	 *  changed as a result of the application of a tree rule; <code>false
	 *  </code> otherwise
	 */
	private static boolean applyRuleToTreeWhere(ProofTree tree, Condition condition) {
		for(Iterator<ProofTreeNode> nodes = tree.getUnclosedNodes(); nodes.hasNext();) {
			ProofTreeNode currentNode = nodes.next();
			for(Iterator<Formula> formulae = currentNode.getFormulae(); formulae.hasNext();) {
				Formula currentFormula = formulae.next();
				if(!currentNode.isTicked(currentFormula) && condition.satisfies(tree, currentNode, currentFormula)) {
					Vector<ProofTreeNode> newLeaves = applyRule(tree, currentNode, currentFormula);
					if(newLeaves.size() > 0 && tree.addLeavesBelow(currentNode, newLeaves)) {
						return(true);
					}
				}
			}
		}
		return(false);
	}

	/**
	 * Apply a tree rule to the given formula in the given node to the tree.
	 * Note that any given formula can only have one tree rule applied to it,
	 * so this method will work on any node/formula combination. No regard is
	 * given to rule preference; this is the caller's responsibility.
	 *
	 * @param tree the tree to which a tree rule is to be applied
	 * @param node the node to which a tree rule is to be applied
	 * @param formula the formula to which a tree rule is to be applied
	 * @return the nodes created as a result of the rule application (the
	 *  caller is responsible for adding these nodes to the tree in a
	 *  semantically correct way)
	 */
	private static Vector<ProofTreeNode> applyRule(ProofTree tree, ProofTreeNode node, Formula formula) {
		String majorOperator = formula.getMajorOperator();
		Vector<Formula> majorOperands = formula.getMajorOperands();
		Vector<Formula> left = new Vector<Formula>();
		Vector<Formula> right = new Vector<Formula>();
		Vector<ProofTreeNode> result = new Vector<ProofTreeNode>();
		if(majorOperator.equals(Formula.DISJUNCTION)) {
			left.add(majorOperands.get(0));
			right.add(majorOperands.get(1));
			result.add(new ProofTreeNode(left));
			result.add(new ProofTreeNode(right));
			node.tickFormula(formula);
		} else if(majorOperator.equals(Formula.CONJUNCTION)) {
			left.add(majorOperands.get(0));
			left.add(majorOperands.get(1));
			result.add(new ProofTreeNode(left));
			node.tickFormula(formula);
		} else if(majorOperator.equals(Formula.IFTHEN)) {
			left.add(majorOperands.get(0).getNegation());
			right.add(majorOperands.get(1));
			result.add(new ProofTreeNode(left));
			result.add(new ProofTreeNode(right));
			node.tickFormula(formula);
		} else if(majorOperator.equals(Formula.IFF)) {
			left.add(majorOperands.get(0));
			left.add(majorOperands.get(1));
			right.add(majorOperands.get(0).getNegation());
			right.add(majorOperands.get(1).getNegation());
			result.add(new ProofTreeNode(left));
			result.add(new ProofTreeNode(right));
			node.tickFormula(formula);
		} else if(majorOperator.startsWith(Formula.FORALL)) {
			Vector<Formula> newFormulae = new Vector<Formula>();
			String var = majorOperator.substring(1);
			Formula subformula = majorOperands.get(0);
			boolean added = false;
			for(Iterator<ProofTreeNode> leaves = tree.getLeavesBelow(node).iterator(); leaves.hasNext();) {
				for(Iterator<String> constants = leaves.next().getConstantsFrom(); constants.hasNext();) {
					Formula newFormula = subformula.substitute(var, constants.next());
					if(!newFormulae.contains(newFormula)) {
						added = true;
						newFormulae.add(newFormula);
					}
				}
			}
			if(!added) {
				newFormulae.add(subformula.substitute(var, "a"));
			}
			result.add(new ProofTreeNode(newFormulae));
		} else if(majorOperator.startsWith(Formula.EXISTS)) {
			String var = majorOperator.substring(1);
			Formula subformula = majorOperands.get(0);
			String con = "";
			for(Iterator<String> constants = node.getConstantsFrom(); constants.hasNext();) {
				con += constants.next();
			}
			String newconstant;
			if(con.equals("")) {
				newconstant = "a";
			} else {
				newconstant = "abcdefghijklmnopqrstuvwxyz".replaceAll("[" + con + "]", "");
				if(newconstant.length() > 0) {
					newconstant = newconstant.substring(0, 1);
				} else {
					newconstant = "*";
				}
			}
			Formula newFormula = subformula.substitute(var, newconstant);
			Vector<Formula> newFormulae = new Vector<Formula>();
			newFormulae.add(newFormula);
			result.add(new ProofTreeNode(newFormulae));
			node.tickFormula(formula);
		} else if(majorOperator.equals(Formula.NEGATION)) {
			String nextMajorOperator = majorOperands.get(0).getMajorOperator();
			Vector<Formula> nextMajorOperands = majorOperands.get(0).getMajorOperands();
			if(nextMajorOperator.equals(Formula.DISJUNCTION)) {
				left.add(nextMajorOperands.get(0).getNegation());
				left.add(nextMajorOperands.get(1).getNegation());
				result.add(new ProofTreeNode(left));
				node.tickFormula(formula);
			} else if(nextMajorOperator.equals(Formula.CONJUNCTION)) {
				left.add(nextMajorOperands.get(0).getNegation());
				right.add(nextMajorOperands.get(1).getNegation());
				result.add(new ProofTreeNode(left));
				result.add(new ProofTreeNode(right));
				node.tickFormula(formula);
			} else if(nextMajorOperator.equals(Formula.IFTHEN)) {
				left.add(nextMajorOperands.get(0));
				left.add(nextMajorOperands.get(1).getNegation());
				result.add(new ProofTreeNode(left));
				node.tickFormula(formula);
			} else if(nextMajorOperator.equals(Formula.IFF)) {
				left.add(nextMajorOperands.get(0));
				left.add(nextMajorOperands.get(1).getNegation());
				right.add(nextMajorOperands.get(0).getNegation());
				right.add(nextMajorOperands.get(1));
				result.add(new ProofTreeNode(left));
				result.add(new ProofTreeNode(right));
				node.tickFormula(formula);
			} else if(nextMajorOperator.startsWith(Formula.FORALL)) {
				left.add(new Formula(Formula.EXISTS + nextMajorOperator.substring(1) + Formula.NEGATION + nextMajorOperands.get(0)));
				result.add(new ProofTreeNode(left));
				node.tickFormula(formula);
			} else if(nextMajorOperator.startsWith(Formula.EXISTS)) {
				left.add(new Formula(Formula.FORALL + nextMajorOperator.substring(1) + Formula.NEGATION + nextMajorOperands.get(0)));
				result.add(new ProofTreeNode(left));
				node.tickFormula(formula);
			} else if(nextMajorOperator.equals(Formula.NEGATION)) {
				left.add(nextMajorOperands.get(0));
				result.add(new ProofTreeNode(left));
				node.tickFormula(formula);
			}
		}
		return(result);
	}

	/**
	 * Returns a condition that prefers rule applications which create an
	 * immediate contradiction.
	 *
	 * @return a condition that prefers rule applications which create an
	 * immediate contradiction
	 */
	private static Condition getMakesContradictionCondition() {
		return(new Condition() {
			public boolean satisfies(ProofTree tree, ProofTreeNode node, Formula formula) {
				Vector<ProofTreeNode> newNodes = applyRule(tree, node, formula);
				if(newNodes.size() == 0) {
					node.untickFormula(formula);
					return(false);
				}
				boolean contradiction = false;
				for(Iterator<ProofTreeNode> leaves = tree.getLeavesBelow(node).iterator(); leaves.hasNext() && !contradiction;) {
					ProofTreeNode leaf = leaves.next();
					for(Iterator<ProofTreeNode> children = newNodes.iterator(); children.hasNext() && !contradiction;) {
						ProofTreeNode child = (ProofTreeNode)children.next().clone();
						tree.addChild(leaf, child);
						contradiction = tree.checkContradictionFrom(child);
						tree.removeChild(leaf, child);
					}
				}
				node.untickFormula(formula);
				return(contradiction);
			}
		});
	}

	/**
	 * Returns a condition that prefers quantifier negation rules.
	 *
	 * @return a condition that prefers quantifier negation rules
	 */
	private static Condition getQuantifierNegationCondition() {
		return(new Condition() {
			public boolean satisfies(ProofTree tree, ProofTreeNode node, Formula formula) {
				String majorOperator = formula.getMajorOperator();
				if(majorOperator.equals(Formula.NEGATION)) {
					String nextOperator = formula.getMajorOperands().get(0).getMajorOperator();
					if(nextOperator.startsWith(Formula.FORALL)) {
						return(true);
					} else if(nextOperator.startsWith(Formula.EXISTS)) {
						return(true);
					} else {
						return(false);
					}
				} else {
					return(false);
				}
			}
		});
	}

	/**
	 * Returns a condition that prefers non-branching sentential rules.
	 *
	 * @return a condition that prefers non-branching sentential rules
	 */
	private static Condition getNonBranchingSententialCondition() {
		return(new Condition() {
			public boolean satisfies(ProofTree tree, ProofTreeNode node, Formula formula) {
				String majorOperator = formula.getMajorOperator();
				if(majorOperator.equals(Formula.DISJUNCTION)) {
					return(false);
				} else if(majorOperator.equals(Formula.CONJUNCTION)) {
					return(true);
				} else if(majorOperator.equals(Formula.IFTHEN)) {
					return(false);
				} else if(majorOperator.equals(Formula.IFF)) {
					return(false);
				} else if(majorOperator.startsWith(Formula.FORALL)) {
					return(false);
				} else if(majorOperator.startsWith(Formula.EXISTS)) {
					return(false);
				} else if(majorOperator.equals(Formula.NEGATION)) {
					String nextOperator = formula.getMajorOperands().get(0).getMajorOperator();
					if(nextOperator.equals(Formula.DISJUNCTION)) {
						return(true);
					} else if(nextOperator.equals(Formula.CONJUNCTION)) {
						return(false);
					} else if(nextOperator.equals(Formula.IFTHEN)) {
						return(true);
					} else if(nextOperator.equals(Formula.IFF)) {
						return(false);
					} else if(nextOperator.startsWith(Formula.FORALL)) {
						return(false);
					} else if(nextOperator.startsWith(Formula.EXISTS)) {
						return(false);
					} else if(nextOperator.equals(Formula.NEGATION)) {
						return(true);
					} else {
						return(false);
					}
				} else {
					return(false);
				}
			}
		});
	}

	/**
	 * Returns a condition that prefers the existential instantiation rule.
	 *
	 * @return a condition that prefers the existential instantiation rule
	 */
	private static Condition getExistentialInstantiationCondition() {
		return(new Condition() {
			public boolean satisfies(ProofTree tree, ProofTreeNode node, Formula formula) {
				return(formula.getMajorOperator().startsWith(Formula.EXISTS));
			}
		});
	}

	/**
	 * Returns a condition that prefers the universal instantiation rule.
	 *
	 * @return a condition that prefers the universal instantiation rule
	 */
	private static Condition getUniversalInstantiationCondition() {
		return(new Condition() {
			public boolean satisfies(ProofTree tree, ProofTreeNode node, Formula formula) {
				return(formula.getMajorOperator().startsWith(Formula.FORALL));
			}
		});
	}

	/**
	 * Returns a condition that prefers branching sentential rules.
	 *
	 * @return a condition that prefers branching sentential rules
	 */
	private static Condition getBranchingSententialCondition() {
		return(new Condition() {
			public boolean satisfies(ProofTree tree, ProofTreeNode node, Formula formula) {
				String majorOperator = formula.getMajorOperator();
				if(majorOperator.equals(Formula.DISJUNCTION)) {
					return(true);
				} else if(majorOperator.equals(Formula.CONJUNCTION)) {
					return(false);
				} else if(majorOperator.equals(Formula.IFTHEN)) {
					return(true);
				} else if(majorOperator.equals(Formula.IFF)) {
					return(true);
				} else if(majorOperator.startsWith(Formula.FORALL)) {
					return(false);
				} else if(majorOperator.startsWith(Formula.EXISTS)) {
					return(false);
				} else if(majorOperator.equals(Formula.NEGATION)) {
					String nextOperator = formula.getMajorOperands().get(0).getMajorOperator();
					if(nextOperator.equals(Formula.DISJUNCTION)) {
						return(false);
					} else if(nextOperator.equals(Formula.CONJUNCTION)) {
						return(true);
					} else if(nextOperator.equals(Formula.IFTHEN)) {
						return(false);
					} else if(nextOperator.equals(Formula.IFF)) {
						return(true);
					} else if(nextOperator.startsWith(Formula.FORALL)) {
						return(false);
					} else if(nextOperator.startsWith(Formula.EXISTS)) {
						return(false);
					} else if(nextOperator.equals(Formula.NEGATION)) {
						return(false);
					} else {
						return(false);
					}
				} else {
					return(false);
				}
			}
		});
	}

	/**
	 * Returns a condition that prefers any rule.
	 *
	 * @return a condition that prefers any rule
	 */
	private static Condition getWildCardCondition() {
		return(new Condition() {
			public boolean satisfies(ProofTree tree, ProofTreeNode node, Formula formula) {
				return(!formula.isAtom());
			}
		});
	}
}

/**
 * The <code>Condition</code> class represents a condition for rule application,
 * i.e., a preference in the order that a rule is applied.
 */
abstract class Condition {
	/**
	 * Answers whether or not an application of a tree rule to the given formula
	 * in the given node in the given tree satisfies a condition to be
	 * determined by implementations of this class.
	 *
	 * @param tree the tree to which a tree rule is to be applied
	 * @param node the node to which a tree rule is to be applied
	 * @param formula the formula to which a tree rule is to be applied
	 * @return <code>true</code> if the condition is satisfied; <code>false
	 *  </code> otherwise
	 */
	public abstract boolean satisfies(ProofTree tree, ProofTreeNode node, Formula formula);
}