/*
 *
 * Copyright (c) 2010, Regents of the University of California
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 *
 * Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * Neither the name of the Lawrence Berkeley National Lab nor the names of its contributors may be used to endorse
 * or promote products derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY,
 * OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */
package org.bbop.phylo.io.panther;

import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;

import org.apache.log4j.Logger;
import org.bbop.phylo.model.Bioentity;
import org.bbop.phylo.model.Family;
import org.bbop.phylo.model.Tree;
import org.bbop.phylo.species.TaxonFinder;
import org.bbop.phylo.util.Constant;

/**
 * Created by suzi on 12/15/14.
 */
public abstract class PantherParser implements PantherParserI {

	private static final Logger log = Logger.getLogger(PantherParser.class);

	public PantherParser() {
		
	}
	
	public boolean parseFamily(Family family, Tree tree) {
		Bioentity root = parsePantherTree(family.getTreeContent());
		if (root != null) {
			tree.growTree(root);
			// Load the attr file to obtain the PTN #s
			List<List<String>> rows = ParsingHack.parsePantherAttr(family.getAttrContent());
			decorateNodes(rows, tree);

			if (tree.getRoot().getNcbiTaxonId() == null) {
				String taxon = TaxonFinder.getTaxonID("LUCA");
				tree.getRoot().setNcbiTaxonId(taxon);
			}
		}
		return root != null;
	}

	public Bioentity parsePantherTree(List<String> treeContents) {
		if (null == treeContents) {
			return null;
		}
		if (0 == treeContents.size()) {
			return null;
		}
		// Modify, if there are no line returns
		if (1 == treeContents.size()) {
			treeContents = ParsingHack.tokenize(treeContents.get(0), Constant.SEMI_COLON);
		}

		Bioentity root = null;

		for (String row : treeContents) {
			if (root == null) {
				root = parseTreeString(row);
			} else {
				int index = row.indexOf(Constant.COLON);
				String anId = row.substring(0, index);
				Bioentity node = IDmap.inst().getGeneByANId(anId);
				if (null == node) {
					log.info("Found data for non-existent annotation node " + anId);
					continue;
				}
				// minus 1 to trim the semi-colon off?
				ParsingHack.parseIDstr(node, row.substring(index + 1));
			}
		}

		return root;

	}

	private Bioentity parseTreeString(String s) {
		Bioentity node = null;
		Bioentity root = null;
		StringTokenizer st = new StringTokenizer(s, Constant.DELIM, true);
		while (st.hasMoreTokens()) {
			String token = st.nextToken();
			if (token.equals(Constant.OPEN_PAREN)) {
				if (null == node) {
					/*
					 * The real root node, first one set
					 */
					node = createNode();
					root = node;
				}
				else {
					Bioentity newChild = createNode();
					List<Bioentity> children = node.getChildren();
					if (node.getChildren() == null) {
						children = new ArrayList<Bioentity>();
					}
					children.add(newChild);
					newChild.setParent(node);
					node.setChildren(children);
					/*
					 * Move down
					 */
					node = newChild;
				}
			}
			else if ((token.equals(Constant.CLOSE_PAREN)) ||
					(token.equals(Constant.COMMA)) ||
					(token.equals(Constant.SEMI_COLON))) {
				// Do nothing
			}
			else {
				int squareIndexStart = token.indexOf(Constant.OPEN_BRACKET);
				int squareIndexEnd = token.indexOf(Constant.CLOSE_BRACKET);
				if (0 == squareIndexStart) {
					String type = token.substring(squareIndexStart, squareIndexEnd + 1);
					/*
					 * This is when the AN number is teased out
					 */
					setTypeAndId(type, node);
				}
				else {
					int index = token.indexOf(Constant.COLON);
					if (0 == index) {
						if (-1 == squareIndexStart) {
							node.setDistanceFromParent(Float.valueOf(token.substring(index+1)).floatValue());
						}
						else {
							node.setDistanceFromParent(Float.valueOf(token.substring((index+1), squareIndexStart)).floatValue());
							String type = token.substring(squareIndexStart, squareIndexEnd + 1);
							/*
							 * This is when the AN number is teased out
							 */
							setTypeAndId(type, node); // this use to be included in setType itself
						}
						/*
						 * Move back up
						 */
						node = (Bioentity) node.getParent();
					} else if (index > 0) {
						Bioentity newChild = createNode();
						if (-1 == squareIndexStart) {
							newChild.setDistanceFromParent(Float.valueOf(token.substring(index+1)).floatValue());
							setTypeAndId(token.substring(0, index), newChild); // this use to be included in setType itself
						}
						else {
							newChild.setDistanceFromParent(Float.valueOf(token.substring((index+1), squareIndexStart)).floatValue());
							String type = token.substring(squareIndexStart, squareIndexEnd + 1);
							/*
							 * This is when the AN number is teased out
							 */
							setTypeAndId(type, newChild); // this use to be included in setType itself
						}
						List<Bioentity> children = node.getChildren();
						if (null == children) {
							children = new ArrayList<Bioentity>();
						}
						/*
						 * Add siblings to current node
						 */
						children.add(newChild);
						newChild.setParent(node);
						node.setChildren(children);
					}
				}
			}
		}
		return root;
	}

	private void setTypeAndId(String nodeType, Bioentity node) {
		if (null == nodeType) {
			return;
		}
		String annot_id;
		node.setTypeCls(Constant.PROTEIN);
		if (!nodeType.startsWith("AN")) {
			node.setType(nodeType);
			// collect the species while we're at it
			int index = nodeType.indexOf("S=");
			if (index >= 0) {
				int endIndex = nodeType.indexOf(Constant.COLON, index);
				if (-1 == endIndex) {
					endIndex = nodeType.indexOf(Constant.CLOSE_BRACKET);
				}
				String species = nodeType.substring(index + "S=".length(), endIndex);
				node.addSpeciesLabel(species);
				String taxon = TaxonFinder.getTaxonID(species);
				if (taxon != null && taxon.length() > 0)
					node.setNcbiTaxonId(taxon);
				else {
					log.info("Could not find taxa ID for " + species + " on node " + node.getDBID());
				}
			}
			// now pick up the node name/id
			index = nodeType.indexOf(Constant.NODE_TYPE_ANNOTATION);
			if (index >= 0) {
				int endIndex = nodeType.indexOf(Constant.COLON, index);
				if (-1 == endIndex) {
					endIndex = nodeType.indexOf(Constant.CLOSE_BRACKET);
				}
				annot_id = nodeType.substring(index + Constant.NODE_TYPE_ANNOTATION_LENGTH, endIndex);
			} else {
				annot_id = null;
			}
		} else {
			annot_id = nodeType;
		}

		if (node.getSpeciesLabel() == null || node.getSpeciesLabel().length() == 0) {
			String taxon = TaxonFinder.getTaxonID("LUCA");
			node.setNcbiTaxonId(taxon);
		}

		// now pick up the node name/id
		if (annot_id != null) {
			if (!annot_id.startsWith("AN"))
				log.info(annot_id + " isn't an AN number");
			if (node.getPaintId() != null && node.getPaintId().length() > 0) {
				log.info(annot_id + "AN number is already set to " + node.getPaintId());
			}
			node.setPaintId(annot_id);
			IDmap.inst().indexByANid(node);
		}

	}

	protected void decorateNodes(List<List<String>> rows, Tree tree) {
		if (null == rows || tree == null) {
			return;
		}
		if (rows.get(0) != null) {
			List<String> header = rows.get(0);
			/* skip the table headers from the first row */
			/* now go after the data */
			for (int i = 1; i < rows.size(); i++) {
				List<String> row = rows.get(i);
				parseAttributeRow (row, header);
			}
		}
	}

	private static final String ACC_TAG = "gi";
	private static final String PROT_TAG = "Protein Id";
	private static final String ORG_TAG = "organism";
	private static final String SYMB_TAG = "gene symbol";

	private void parseAttributeRow(List<String> row, List<String> header) {
		String id = row.get(0);
		String ptn = row.get(row.size() - 1);
		Bioentity node = ParsingHack.findThatNode(id);
		if (node == null) {
			/*
			 * This should never happen!
			 */
			log.error("This node is not in the family tree: " + id + " - " + ptn);
			return;
		} 
		if (node.getPersistantNodeID() != null && node.getPersistantNodeID().equals(ptn)) {
			log.error("Yikes, " + node.getPersistantNodeID() + " does not equal " + ptn);
			log.error("\tGene is " + id);
		} 
		else {
			node.setPersistantNodeID("PANTHER", ptn);
			IDmap.inst().indexNodeByPTN(node);
		}

		for (int j = 0; j < row.size(); j++) {
			String tag = header.get(j);
			String value = row.get(j);
			value = value != null ? value.trim() : Constant.STR_EMPTY;
			if (tag.equals(ACC_TAG) || tag.equals(PROT_TAG)) {
				if (node.getSeqId() == null) {
					log.info("accession after the fact for: " + value);
				}
			} else if (tag.equals(ORG_TAG)) {
				node.addSpeciesLabel(value);
				if (node.getNcbiTaxonId() == null) {
					String taxon = TaxonFinder.getTaxonID(value);
					node.setNcbiTaxonId(taxon);
				}
			} else if (tag.equals(SYMB_TAG)) {
				node.setSymbol(value);
			}
		}
	}
}

