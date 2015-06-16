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
 * The <code>ProofTree</code> class represents a proof tree. A proof tree is
 * essentially a binary tree comprised of <code>ProofTreeNode</code> objects as
 * nodes. The tree records only its root, and leaves bookkeeping to its nodes.
 */
public class ProofTree {
	/**
	 * The root node of this proof tree.
	 */
	private ProofTreeNode root;

	/**
	 * Creates a new <code>ProofTree</code> object. The root of the tree will
	 * be a node containing the specified formulae.
	 *
	 * @param formulae the formulae to be placed in the root node
	 */
	public ProofTree(Vector<Formula> formulae) {
		root = new ProofTreeNode(formulae);
	}

	/**
	 * Creates a new <code>ProofTree</code> object with the specified root.
	 *
	 * @param root the root of the tree
	 */
	public ProofTree(ProofTreeNode root) {
		this.root = root;
	}

	/**
	 * Returns the root of this tree.
	 *
	 * @return the root of this tree
	 */
	public ProofTreeNode getRoot() {
		return(this.root);
	}

	/**
	 * Adds a child to the given node in the tree. The node will be added as
	 * either the left child or the right child, depending on which is not yet
	 * currently occupied. If both are already occupied, an <code>
	 * IllegalArgumentException</code> is thrown. The parent and child
	 * relationships of each node are updated accordingly.
	 *
	 * @param parent the parent of the node to be added
	 * @param child the child to be added to the specified parent
	 * @throws IllegalArgumentException if the parent already has two children
	 */
	public void addChild(ProofTreeNode parent, ProofTreeNode child) {
		if(parent.getLeftChild() == null) {
			parent.setLeftChild(child);
			child.setParent(parent);
		} else if(parent.getRightChild() == null) {
			parent.setRightChild(child);
			child.setParent(parent);
		} else {
			throw new IllegalArgumentException("too many children");
		}
	}

	/**
	 * Removes a child of the given node in the tree. No operation is performed
	 * if the given node does not have the specified child. The parent and child
	 * relationships of each node are updated accordingly.
	 *
	 * @param parent the parent of the node to be removed
	 * @param child the child to be removed from the specified parent
	 */
	public void removeChild(ProofTreeNode parent, ProofTreeNode child) {
		if(parent.getLeftChild() == child) {
			parent.setLeftChild(null);
			child.setParent(null);
		} else if(parent.getRightChild() == child) {
			parent.setRightChild(null);
			child.setParent(null);
		}
	}

	/**
	 * Returns a <code>Vector</code> containing all of the leaves of the tree
	 * below the given node.
	 *
	 * @param parent the node under which all leaves should be returned
	 * @return all leaves under the specified node
	 */
	public Vector<ProofTreeNode> getLeavesBelow(ProofTreeNode parent) {
		Vector<ProofTreeNode> result = new Vector<ProofTreeNode>();
		if(this.isLeaf(parent) && !parent.isClosed()) {
			result.add(parent);
		} else {
			if((parent.getLeftChild() != null) && (!parent.getLeftChild().isClosed())) {
				result.addAll(getLeavesBelow(parent.getLeftChild()));
			}
			if((parent.getRightChild() != null) && (!parent.getRightChild().isClosed())) {
				result.addAll(getLeavesBelow(parent.getRightChild()));
			}
		}
		return(result);
	}

	/**
	 * Adds as children all the specified nodes to the leaves of the tree below
	 * the given node. Nodes are closed as appropriate.
	 *
	 * @param parent the node under which the leaves are to be updated
	 * @param children the children to be added under each leaf
	 * @return <code>true</code> if the tree changed as a result of this
	 * operation; <code>false</code> otherwise
	 */
	public boolean addLeavesBelow(ProofTreeNode parent, Vector<ProofTreeNode> children) {
		boolean changed = false;
		for(Iterator<ProofTreeNode> i = this.getLeavesBelow(parent).iterator(); i.hasNext();) {
			ProofTreeNode leaf = i.next();
			for(Iterator<ProofTreeNode> j = children.iterator(); j.hasNext();) {
				ProofTreeNode child = (ProofTreeNode)j.next().clone();
				int already = 0;
				int total = 0;
				for(Iterator<Formula> k = child.getFormulae(); k.hasNext();) {
					total++;
					if(leaf.containsFormulaFrom(k.next())) {
						already++;
					}
				}
				if(already < total) {
					this.addChild(leaf, child);
					if(this.checkContradictionFrom(child)) {
						child.close();
					}
					changed = true;
				}
			}
		}
		return(changed);
	}

	/**
	 * Answers whether or not the specified node is a leaf in this tree. A node
	 * is a leaf if and only if it has no children.
	 *
	 * @param node the node to be tested for being a leaf
	 * @return <code>true</code> if the specified node is a leaf in this tree;
	 *  <code>false</code> otherwise
	 */
	private boolean isLeaf(ProofTreeNode node) {
		return((node.getLeftChild() == null) && (node.getRightChild() == null));
	}

	/**
	 * Answers the size of this tree, i.e., the number of nodes in the tree.
	 *
	 * @return the size of the tree
	 */
	public int size() {
		return(sizeFrom(root));
	}

	/**
	 * Answers the size of this tree below the given node (inclusive.)
	 *
	 * @return the size of the tree below the given node (inclusive.)
	 * @see #size()
	 */
	private int sizeFrom(ProofTreeNode node) {
		if(node == null) {
			return(0);
		} else {
			return(1 + sizeFrom(node.getLeftChild()) + sizeFrom(node.getRightChild()));
		}
	}

	/**
	 * Returns an <code>Iterator</code> over the unclosed nodes of this tree.
	 *
	 * @return an <code>Iterator</code> over the unclosed nodes of this tree
	 * @see java.util.Iterator
	 */
	public Iterator<ProofTreeNode> getUnclosedNodes() {
		return(getUnclosedNodesBelow(root).iterator());
	}

	/**
	 * Returns an <code>Vector</code> of the unclosed nodes of this tree below
	 * the given node.
	 *
	 * @return all of the unclosed nodes in this tree below the given node
	 * @see #getUnclosedNodes()
	 * @see java.util.Iterator
	 */
	private Vector<ProofTreeNode> getUnclosedNodesBelow(ProofTreeNode parent) {
		Vector<ProofTreeNode> result = new Vector<ProofTreeNode>();
		if(!parent.isClosed()) {
			result.add(parent);
		}
		if((parent.getLeftChild() != null) && (!parent.getLeftChild().isClosed())) {
			result.addAll(getUnclosedNodesBelow(parent.getLeftChild()));
		}
		if((parent.getRightChild() != null) && (!parent.getRightChild().isClosed())) {
			result.addAll(getUnclosedNodesBelow(parent.getRightChild()));
		}
		return(result);
	}

	/**
	 * Answers whether a contradiction exists between this node and any node
	 * above it.
	 *
	 * @param node the node to begin checking for contradictions from
	 * @return <code>true</code> if this node contradicts with any node above
	 *  it; <code>false</code> otherwise
	 */
	public boolean checkContradictionFrom(ProofTreeNode node) {
		return(checkContradictionBetween(node, node));
	}

	/**
	 * Answers whether a contradiction exists between one node and any node
	 * beteen it and another node.
	 *
	 * @param start the node to begin checking for contradictions from
	 * @param current the node to stop checking for contradictions from
	 * @return <code>true</code> if this node contradicts with any node above
	 *  it up to <code>current</code>; <code>false</code> otherwise
	 * @see #checkContradictionFrom(ProofTreeNode)
	 */
	private boolean checkContradictionBetween(ProofTreeNode start, ProofTreeNode current) {
		if(start.contradicts(current)) {
			return(true);
		} else if(current == this.root) {
			return(false);
		} else {
			return(checkContradictionBetween(start, current.getParent()));
		}
	}

	/**
	 * Answers whether or not all leaves of this tree close.
	 *
	 * @return <code>true</code> if all leaves of this tree close; <code>false
	 *  </code> otherwise
	 */
	public boolean closes() {
		return(closesFrom(root));
	}

	/**
	 * Answers whether or not all leaves of this tree below the given node
	 * close.
	 *
	 * @param node the node to start checking from
	 * @return <code>true</code> if all leaves of this tree below the given node
	 *  close; <code>false</code> otherwise
	 */
	public boolean closesFrom(ProofTreeNode node) {
		if(node.isClosed()) {
			return(true);
		} else {
			if(node.getLeftChild() != null) {
				if(node.getRightChild() != null) {
					return(closesFrom(node.getLeftChild()) && closesFrom(node.getRightChild()));
				} else {
					return(closesFrom(node.getLeftChild()));
				}
			} else {
				if(node.getRightChild() != null) {
					return(closesFrom(node.getRightChild()));
				} else {
					return(false);
				}
			}
		}
	}

	/**
	 * Returns a string representation of this proof tree.
	 *
	 * @return a string representation of this proof tree
	 */
	public String toString() {
		return(this.toStringFrom(this.root, 0));
	}

	/**
	 * Returns a string representation of this proof tree from the given node
	 * with the given level of indentation for pretty-printing purposes.
	 *
	 * @param node the node to begin from
	 * @param level the levels of indentation, i.e., the height of a node
	 * @return a string representation of this proof tree below the given node
	 */
	private String toStringFrom(ProofTreeNode node, int level) {
		if(node == null) {
			return("");
		} else {
			String result = "";
			for(int i = 0; i < level; i++) {
				result += "|   ";
			}
			result += node.toString() + "\n";
			result += this.toStringFrom(node.getLeftChild(), level + 1);
			result += this.toStringFrom(node.getRightChild(), level + 1);
			return(result);
		}
	}
}