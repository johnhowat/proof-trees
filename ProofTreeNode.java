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
 * The <code>ProofTreeNode</code> class represents a node in a proof tree. Nodes
 * have one or more <code>Formula</code> objects associated with them. Each
 * Formula may be ``ticked'', so that will no longer be under consideration in
 * algorithms involving the node. A node may also become ``closed'' if it
 * contradicts with itself or any of its ancestors (although it is the caller's
 * responsibility to ask the node to check for this.)
 * <p>
 * A proof tree node functions very similar to a node in a binary tree, although
 * it may have only one child. A proof tree node keeps track of its parent and
 * children.
 */
class ProofTreeNode implements Cloneable {
	/**
	 * A <code>Vector</code> containing the <code>Formula</code> objects
	 * contained within this node.
	 */
	private Vector<Formula> formulae;

	/**
	 * The parent of this node, or <code>null</code> if no parent exists (i.e.,
	 * this node is the root of the tree.)
	 */
	private ProofTreeNode parent;

	/**
	 * The right child of this node, or <code>null</code> if no right child
	 * exists.
	 */
	private ProofTreeNode leftChild;

	/**
	 * The left child of this node, or <code>null</code> if no left child
	 * exists.
	 */
	private ProofTreeNode rightChild;

	/**
	 * An array containing booleans representing whether the corresponding
	 * formula in the formulae Vector is ticked.
	 */
	private boolean[] ticked;

	/**
	 * A boolean indicating whether or not this node is closed.
	 */
	private boolean closed;

	/**
	 * Creates a new <code>ProofTree</code> node from the given <code>Vector
	 * </code> of <code>Formula</code> objects. The parent and children of the
	 * node must be set manually after construction.
	 *
	 * @param formulae a <code>Vector</code> of <code>Formula</code> objects
	 *  that this node will represent
	 */
	public ProofTreeNode(Vector<Formula> formulae) {
		this.formulae = formulae;
		this.ticked = new boolean[this.formulae.size()];
		for(int i = 0; i < this.ticked.length; i++) {
			this.ticked[i] = false;
		}
		this.closed = false;
	}

	/**
	 * Returns an <code>Iterator</code> over the <code>Formula</code> objects
	 * contained in this node.
	 *
	 * @return an <code>Iterator</code> over the given <code>Formula</code>
	 *  objects contained in this node
	 * @see java.util.Iterator
	 */
	public Iterator<Formula> getFormulae() {
		return(this.formulae.iterator());
	}

	/**
	 * Returns the parent of this node, or <code>null</code> if no parent exists
	 * (i.e., this node is the root of the tree.)
	 *
	 * @return the parent of this node, or <code>null</code> if no parent exists
	 */
	public ProofTreeNode getParent() {
		return(this.parent);
	}

	/**
	 * Returns the left child of this node, or <code>null</code> if no left
	 * child exists.
	 *
	 * @return the left child of this node, or <code>null</code> if no left
	 *  child exists.
	 */
	public ProofTreeNode getLeftChild() {
		return(this.leftChild);
	}

	/**
	 * Returns the right child of this node, or <code>null</code> if no right
	 * child exists.
	 *
	 * @return the right child of this node, or <code>null</code> if no right
	 *  child exists.
	 */
	public ProofTreeNode getRightChild() {
		return(this.rightChild);
	}

	/**
	 * Sets the parent of this node to be the given node. It is the caller's
	 * responsibility to set one of the parent's children to be this node.
	 *
	 * @param parent the new parent of this node
	 */
	public void setParent(ProofTreeNode parent) {
		this.parent = parent;
	}

	/**
	 * Sets the left child of this node to be the given node. It is the caller's
	 * responsibility to set the child's parent to be this node.
	 *
	 * @param leftChild the new left child of this node
	 */
	public void setLeftChild(ProofTreeNode leftChild) {
		this.leftChild = leftChild;
	}

	/**
	 * Sets the right child of this node to be the given node. It is the
	 * caller's responsibility to set the child's parent to be this node.
	 *
	 * @param rightChild the new right child of this node
	 */
	public void setRightChild(ProofTreeNode rightChild) {
		this.rightChild = rightChild;
	}

	/**
	 * Answers whether or not this node contradicts with the specified node. Two
	 * nodes contradict if and only one formula of this node contradicts with
	 * one formula in the other (not necessarily distinct) node.
	 *
	 * @param n a node to be tested for contradiction with this one
	 * @return <code>true</code> if this node contradicts the given node; <code>
	 *  false</code> otherwise
	 * @see Formula#contradicts(Formula)
	 */
	public boolean contradicts(ProofTreeNode n) {
		for(Iterator<Formula> i = this.formulae.iterator(); i.hasNext();) {
			Formula current = i.next();
			for(Iterator<Formula> j = n.formulae.iterator(); j.hasNext();) {
				if(current.contradicts(j.next())) {
					return(true);
				}
			}
		}
		return(false);
	}

	/**
	 * Returns an <code>Iterator</code> over the non-bound variables of in this
	 * node. The non-bound variables of a node are precisely the union of the
	 * non-bound variables in each of the node's formulae. Duplicates will not
	 * be included.
	 *
	 * @return an <code>Iterator</code> over the non-bound variables in this
	 *  node
	 * @see Formula#getConstants()
	 * @see java.util.Iterator
	 */
	public Iterator<String> getConstants() {
		Vector<String> result = new Vector<String>();
		for(Iterator<Formula> i = this.formulae.iterator(); i.hasNext();) {
			for(Iterator<String> j = i.next().getConstants().iterator(); j.hasNext();) {
				String current = j.next();
				if(!result.contains(current)) {
					result.add(current);
				}
			}
		}
		return(result.iterator());
	}

	/**
	 * Returns an <code>Iterator</code> over the non-bound variables of in this
	 * node and all nodes above it. 
	 *
	 * @return an <code>Iterator</code> over the non-bound variables in this
	 *  node and all nodes above it
	 * @see #getConstants()
	 * @see java.util.Iterator
	 */
	public Iterator<String> getConstantsFrom() {
		Vector<String> result = new Vector<String>();
		ProofTreeNode current = this;
		while(current != null && !current.isClosed()) {
			for(Iterator<String> i = current.getConstants(); i.hasNext();) {
				String constant = i.next();
				if(!result.contains(constant)) {
					result.add(constant);
				}
			}
			current = current.getParent();
		}
		return(result.iterator());
	}

	/**
	 * Answers whether or not this node contains the given formula.
	 *
	 * @param formula the formula to be tested for
	 * @return <code>true</code> if this node contains the given formula; <code>
	 *  false</code> otherwise
	 */
	public boolean containsFormula(Formula formula) {
		return(this.formulae.contains(formula));
	}

	/**
	 * Answers whether or not this node or any node above it contains the given
	 * formula.
	 *
	 * @param formula the formula to be tested for
	 * @return <code>true</code> if this node or any node above it contains the
	 *  given formula; <code>false</code> otherwise
	 */
	public boolean containsFormulaFrom(Formula formula) {
		ProofTreeNode current = this;
		while(current != null && !current.isClosed()) {
			if(current.containsFormula(formula)) {
				return(true);
			}
			current = current.getParent();
		}
		return(false);
	}

	/**
	 * Closes this node.
	 */
	public void close() {
		this.closed = true;
	}

	/**
	 * Ticks the given formula inside this node.
	 *
	 * @param formula the formula to be ticked
	 */
	public void tickFormula(Formula formula) {
		this.ticked[this.formulae.indexOf(formula)] = true;
	}

	/**
	 * Unticks the given formula inside this node.
	 *
	 * @param formula the formula to be unticked
	 */
	public void untickFormula(Formula formula) {
		this.ticked[this.formulae.indexOf(formula)] = false;
	}

	/**
	 * Answers whether or not this node is closed.
	 *
	 * @return <code>true</code> if this node is closed; <code>false</code>
	 *  otherwise
	 */
	public boolean isClosed() {
		return(this.closed);
	}

	/**
	 * Answers whether or not the given formula is ticked in this node.
	 *
	 * @param formula the formula to be checked
	 * @return <code>true</code> if the given formula is ticked in this node;
	 *  <code>false</code> otherwise
	 */
	public boolean isTicked(Formula formula) {
		return(this.ticked[this.formulae.indexOf(formula)]);
	}

	/**
	 * Answers whether or not this <code>ProofTreeNode</code> is equal to
	 * another object. A necessary condition for an object being equal to a
	 * <code>ProofTreeNode</code> is that the object is an instance of <code>
	 * ProofTreeNode</code>. Beyond this, two proof tree nodes are equal if and
	 * only if they have the same <code>Vector</code> of formulae.
	 *
	 * @param obj the <code>Object</code> to be tested for equality
	 * @return <code>true</code> if the specified object is equal to this
	 *	<code>ProofTreeNode</code>; <code>false</code> otherwise
	 * @see Formula#equals(Object)
	 */
	public boolean equals(Object obj) {
		if(!(obj instanceof ProofTreeNode)) {
			return(false);
		} else {
			ProofTreeNode n = (ProofTreeNode)obj;
			return(this.formulae.equals(n.formulae));
		}
	}

	/**
	 * Returns a string representation of this node.
	 *
	 * @return a string representation of this node
	 * @see Formula#toString()
	 */
	public String toString() {
		String result = "";
		for(Iterator<Formula> i = this.formulae.iterator(); i.hasNext();) {
			Formula formula = i.next();
			result += formula;
			if(i.hasNext()) {
				result += ", ";
			}
		}
		result += this.isClosed() ? " [X]" : "";
		return(result);
	}

	/**
	 * Returns a copy of this node containing all of the formulae of this node.
	 * Note all formulae of the new node will be unticked and the node will be
	 * unclosed. The new node's parent and children must be set by the caller.
	 *
	 * @return a copy of this node
	 */
	public Object clone() {
		return(new ProofTreeNode(this.formulae));
	}
}