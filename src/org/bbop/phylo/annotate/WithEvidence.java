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
package org.bbop.phylo.annotate;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.bbop.phylo.model.Bioentity;
import org.bbop.phylo.model.GeneAnnotation;
import org.bbop.phylo.model.Tree;
import org.bbop.phylo.owl.OWLutil;

public class WithEvidence {

//	private static Logger log = Logger.getLogger(WithEvidence.class);

	private List<String> exp_withs;
	private List<GeneAnnotation> regulator_of;
	private List<String> notted_withs;
	private int qualifiers;

	public WithEvidence(Tree tree, Bioentity node, String go_id) {
		initWiths(tree, node, go_id);
	}

	public int getWithQualifiers() {
		return qualifiers;
	}

	public List<String> getExpWiths() {
		List<String> all_evidence = new ArrayList<>();
		if (exp_withs.size() > 0 || regulator_of.size() > 0) {
			if (exp_withs.size() > 0) {
				all_evidence.addAll(exp_withs);
			} else {
				for (GeneAnnotation annot : regulator_of) {
					all_evidence.add(annot.getBioentityObject().getId());
				}
			}
		} else if (notted_withs.size() > 0) {
			all_evidence.addAll(notted_withs);
		}
		return all_evidence;
	}

	public boolean isExperimentalNot() {
		return notted_withs.size() > 0 && exp_withs.size() == 0 && regulator_of.size() == 0;
	}

	public boolean lacksEvidence() {
		return exp_withs.size() == 0 && notted_withs.size() == 0 && regulator_of.size() == 0;
	}

	public List <String> getNottedWiths () {
		return notted_withs;
	}
	
	public List<GeneAnnotation> regulates() {
		if (exp_withs.size() == 0) {
			return regulator_of;
		} else {
			return new ArrayList<>();
		}
	}

	private void initWiths(Tree tree, Bioentity node, String go_id) {
		/*
		 * First gather all of the gene nodes leaves that may have provided this term
		 */
		List<Bioentity> leaf_list = tree.getLeafDescendants(node);
		exp_withs = new ArrayList<>();
		notted_withs = new ArrayList<> ();
		regulator_of = new ArrayList<> ();

		qualifiers = 0;
		for (Bioentity leaf : leaf_list) {
			List<GeneAnnotation> exp_annotations = AnnotationUtil.getExperimentalAssociations(leaf);
			if (exp_annotations != null && !exp_annotations.isEmpty()) {
				for (Iterator<GeneAnnotation> it_assoc = exp_annotations.iterator(); it_assoc.hasNext() && !exp_withs.contains(leaf.getId());) {
					GeneAnnotation exp_assoc = it_assoc.next();
					String exp_term = exp_assoc.getCls();
						/*
						 * Is the term in question (go_id) a parental/broader term than
						 * the term associated to the leaf node (exp_term)
						 */
					boolean add = (exp_term.equals(go_id)) || OWLutil.inst().moreSpecific(exp_term, go_id);
					
                    /*
                    * Don't add this node if it is already included.
                     */
					if (add) {
						add = addUnique(exp_withs, leaf.getId(), add);
                    }
                    if (add) {
						/*
						 * The code below is carrying out an unrelated function
						 * Namely to see if any of the experimental nodes that provide the supporting evidence are qualified
						 * Doing this here, rather than as a separate function to avoid recursing down the tree twice
						 */
						if (exp_assoc.hasQualifiers() && exp_term.equals(go_id)) {
							if (exp_assoc.isColocatesWith())
								qualifiers |= GeneAnnotation.COLOCALIZES_MASK;
							if (exp_assoc.isContributesTo())
								qualifiers |= GeneAnnotation.CONTRIBUTES_TO_MASK;
							if (exp_assoc.isIntegralTo())
								qualifiers |= GeneAnnotation.INTEGRAL_TO_MASK;
						}
						if (exp_assoc.isNegated()) {
							addUnique(notted_withs, leaf.getId(), true);
							exp_withs.remove(leaf.getId());
						}
					} else {
						if (OWLutil.inst().moreSpecific(exp_term, go_id, true)) {
							boolean add_it = true;
							for (GeneAnnotation annot : regulator_of) {
								add_it &= !annot.getCls().equals(exp_term);
							}
							if (add_it) {
								regulator_of.add(exp_assoc);
							}
						}
					}
				}
			}
		}
	}
	
	private boolean addUnique(List<String> withs, String id, boolean add) {
        for (String with_id : withs) {
            add &= !with_id.equals(id);
        }
        if (add) {
        	withs.add(id);
        }
        return add;
	}
}

