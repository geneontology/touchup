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


import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Date;
import java.util.List;

import org.apache.log4j.Logger;
import org.bbop.phylo.gaf.GafRecorder;
import org.bbop.phylo.model.Bioentity;
import org.bbop.phylo.model.Family;
import org.bbop.phylo.model.GeneAnnotation;
import org.bbop.phylo.model.Tree;
import org.bbop.phylo.owl.OWLutil;
import org.bbop.phylo.tracking.LogAction;
import org.bbop.phylo.tracking.LogEntry;
import org.bbop.phylo.tracking.LogEntry.LOG_ENTRY_TYPE;
import org.bbop.phylo.util.Constant;
import org.bbop.phylo.util.TaxonChecker;

public class PaintAction {

	private static PaintAction INSTANCE;

	private static Logger log = Logger.getLogger(PaintAction.class);

	/**
	 * Provide a thread-safe formatter for a GAF date.
	 */
	public static final ThreadLocal<DateFormat> GAF_Date_Format = new ThreadLocal<DateFormat>() {

		@Override
		protected DateFormat initialValue() {
			return new SimpleDateFormat("yyyyMMdd");
		}

	};

	private PaintAction() {
	}

	public static PaintAction inst() {
		if (INSTANCE == null) {
			INSTANCE = new PaintAction();
		}
		return INSTANCE;
	}

	public LOG_ENTRY_TYPE isValidTerm(String go_id, Bioentity node, Tree tree) {
		/*
		 * Can't drop onto a pruned node
		 */
		if (node.isPruned()) {
			return LogEntry.LOG_ENTRY_TYPE.PRUNE;
		}

		if (OWLutil.inst().isExcluded(go_id)) {
			/*
			Can't use terms that are merely for the logic of the ontology
			and not relevant or informative for the biology
			 */
			return (LOG_ENTRY_TYPE.EXCLUDED);
		}
		// check to make sure that this term is more specific than any inherited terms
		// and the node is not annotated to this term already
		if (AnnotationUtil.isAnnotatedToTerm(node.getAnnotations(), go_id) != null) {
			return (LogEntry.LOG_ENTRY_TYPE.ALREADY_ASSOCIATED);
		}

		// make sure that the term being annotated is related to terms in the descendants
		WithEvidence withs = new WithEvidence(tree, node, go_id);
		if (withs.lacksEvidence()) {
			return (LogEntry.LOG_ENTRY_TYPE.UNSUPPORTED);
		}
		/*
		 *  check to make sure that this term is more generic than directly annotated descendants
		 * if all of them are more general, then disallow the annotation
		 */
		if (OWLutil.inst().descendantsAllBroader(node, go_id, true)) {
			return (LogEntry.LOG_ENTRY_TYPE.TOO_SPECIFIC);
		}
		// applicable term for this taxon?
		if (!TaxonChecker.checkTaxons(tree, node, go_id, true)) {
			return (LogEntry.LOG_ENTRY_TYPE.WRONG_TAXA);
		}
		return null;
	}

	/*
	 * Called after a drop of a term onto a node in the tree or when loading a GAF file
	 */
	public GeneAnnotation propagateAssociation(Family family, Bioentity node, String go_id, WithEvidence withs, String date, int qualifiers) {
		// includes regulation children as well
		List<String> exp_withs = withs.getExpWiths();
		boolean negate = withs.isExperimentalNot();

		int go_qualifiers = getGOqualifiers(qualifiers);
		List<String> top_with = new ArrayList<> ();
		top_with.add(node.getId());

		GeneAnnotation assoc = _propagateAssociation(node,
				go_id,
				go_qualifiers,
				family,
				family.getReference(),
				date,
				negate,
				withs.regulates(),
				top_with,
				exp_withs);

		if (!negate) {
			removeMoreGeneralTerms(node, go_id);
		} else {
			// remove more specific terms TODO
		}
		
		/* bit of a cheat, the null date indicates this was an interactive, 
		 * live annotation through the UI as opposed to an annotation that
		 * happens when reloading
		 */
		if (date == null) {
			filterOutLosses(family, node, assoc);
		}
		
		LogAction.inst().logAssociation(node, assoc);

		return assoc;
	}

	public void filterOutLosses(Family family, Bioentity node, GeneAnnotation assoc) {
		String go_id = assoc.getCls();
		// Check that this GO term is valid for all descendants (false param indicates: not a check on ancestral IBD node)
		boolean valid_for_all_descendents = TaxonChecker.checkTaxons(family.getTree(), node, go_id, false);

		if (!valid_for_all_descendents) {
			// The GO term is not valid for all the leaves, perhaps it's all of them
			boolean not_found_in_taxon = !TaxonChecker.checkTaxons(family.getTree(), node, go_id, true);
			if (not_found_in_taxon) {
				log.debug("Negating annot to " + go_id + " in " + node.getSpeciesLabel());
				setNot(family, node, assoc, Constant.LOSS_OF_FUNCTION, true, null);
			} else {
				List<Bioentity> children = node.getChildren();
				for (Bioentity child : children) {
					List<GeneAnnotation> child_assocs = new ArrayList<>();
					child_assocs.addAll(child.getAnnotations());
					for (GeneAnnotation child_assoc : child_assocs) {
						String child_go_id = child_assoc.getCls();
						if (child_go_id.equals(go_id)) {
							if (!child_assoc.isNegated()) {
								filterOutLosses(family, child, child_assoc);
							}
						}
					}
				}
			}
		}
	}

	private GeneAnnotation _propagateAssociation(Bioentity node,
			String go_id,
			int qualifiers,
			Family family,
			String reference,
			String date,
			boolean negate,
			List<GeneAnnotation> curator_inference,
			List<String> top_with,
			List<String> exp_withs) {
		GeneAnnotation top_assoc = null;
		/**
		 * Only proceed if this is not one of the original sources of information for this association
		 * and this node is not yet annotated to either this term
		 */
		if (!exp_withs.contains(node.getId()) && 
				AnnotationUtil.isAnnotatedToTerm(node.getAnnotations(), go_id) == null) {
			GeneAnnotation assoc;
			if (top_with.contains(node.getId())) {
				assoc = createAnnotation(node, go_id, qualifiers, family, reference, date, true, negate, curator_inference, exp_withs);
				// not dirty if this is restoring annotations from a saved file
				//			DirtyIndicator.inst().dirtyGenes(date == null);
				top_assoc = assoc;
			} else {
				assoc = createAnnotation(node, go_id, qualifiers, family, reference, date, false, negate, curator_inference, top_with);
			}

			/*
			 * Doing this afterwards to avoid examining it in the above operation
			 */
			node.addAnnotation(assoc);

			/*
			 * Make the top ancestral gene in this branch of the gene family the source of information
			 */
			List<Bioentity> children = node.getChildren();
			if (children != null) {
				for (Bioentity child : children) {
					if (!child.isPruned()) {
						_propagateAssociation(child,
								go_id,
								qualifiers,
								family,
								reference,
								date,
								negate,
								curator_inference,
								top_with,
								exp_withs);
					}
				}
			}
		}
		return top_assoc;
	}

	private GeneAnnotation createAnnotation(Bioentity node,
			String go_id,
			int qualifiers,
			Family family,
			String reference,
			String date,
			boolean is_MRC,
			boolean negate,
			List<GeneAnnotation> curator_inference,
			List<String> withs) {
		GeneAnnotation assoc = new GeneAnnotation();
		assoc.setBioentity(node.getId());
		assoc.setBioentityObject(node);
		assoc.setCls(go_id);
		assoc.setQualifiers(qualifiers);
		assoc.addReferenceId(reference);
		assoc.setAspect(OWLutil.inst().getAspect(go_id));
		assoc.setAssignedBy(Constant.PAINT_AS_SOURCE);
		if (date == null) {
			date = getDate();
		}
		assoc.setLastUpdateDate(date);

		assoc.setDirectMRC(is_MRC);
		assoc.setDirectNot(is_MRC && negate);
		/*
		 * propagate negation...
		 */
		assoc.setIsNegated(negate);
		String evidence_code;
		evidence_code = is_MRC ? Constant.DESCENDANT_EVIDENCE_CODE : Constant.ANCESTRAL_EVIDENCE_CODE;
		if (curator_inference.size() > 0) {
			GafRecorder.inst().recordQuestionedAnnotationInGAF(curator_inference, family);
		}
		assoc.setEvidence(evidence_code, null);
		assoc.setWithInfos(withs);
		return assoc;
	}

	private String getDate() {
		long timestamp = System.currentTimeMillis();
		/* Date appears to be fixed?? */
		Date annot_date = new Date(timestamp);
		String dateString = "";
		if (annot_date != null) {
			dateString = GAF_Date_Format.get().format(annot_date);
		}
		return dateString;
	}

	public void propagateAssociation(Family family, GeneAnnotation association) {
		Bioentity node = association.getBioentityObject();
		List<String> top_with = new ArrayList<> ();
		top_with.add(node.getId());
		node.addAnnotation(association);

		WithEvidence withs = new WithEvidence(family.getTree(), node, association.getCls());
		boolean negate = withs.isExperimentalNot();
		List<String> exp_withs = withs.getExpWiths();

		/*
		 * Make the top ancestral gene in this branch of the gene family the source of information
		 */
		List<Bioentity> children = node.getChildren();
		if (children != null) {
			for (Bioentity child : children) {
				if (!child.isPruned()) {
					_propagateAssociation(child,
							association.getCls(),
							association.getQualifiers(),
							family,
							association.getReferenceIds().get(0),
							association.getLastUpdateDate(),
							negate,
							withs.regulates(),
							top_with,
							exp_withs);
				}
			}
		}
		removeMoreGeneralTerms(node, association.getCls());
	}

	public void restoreExpAssociation(Family family, GeneAnnotation assoc) {
		Bioentity node = assoc.getBioentityObject();
		if (node.isLeaf()) {
			node.addAnnotation(assoc);
		} else {
			propagateAssociation(family, assoc);
		}
	}

	private void removeMoreGeneralTerms(Bioentity node, String go_id) {
		removeMoreGeneralTermsFromNode(node, go_id);
		List<Bioentity> children = node.getChildren();
		if (children != null) {
			for (Bioentity child : children) {
				removeMoreGeneralTerms(child, go_id);
			}
		}
	}

	private void removeMoreGeneralTermsFromNode(Bioentity node, String go_id) {
		/*
		 * remove any redundant annotations that have previously been done by PAINT curators
		 * that are less specific than the new association that is being added.
		 * That is: a descendant protein was annotated earlier to a more general term
		 * and now the curator is adding a more specific term to a more ancestral branch of the family
		 */
		List<GeneAnnotation> current_set = node.getAnnotations();
		List<GeneAnnotation> removal = new ArrayList<> ();
		if (current_set != null) {
			for (GeneAnnotation assoc : current_set) {
				if (AnnotationUtil.isPAINTAnnotation(assoc)) {
					String check_term = assoc.getCls();
					if (!go_id.equals(check_term) && OWLutil.inst().moreSpecific(go_id, check_term)) {
						removal.add(assoc);
						//						if (removed != null)
						//							removed.add(assoc);
					}
				}
			}
			for (GeneAnnotation remove : removal) {
				_removeAssociation(node, remove.getCls());
			}
		}
	}

	public void pruneBranch(Bioentity node, boolean log_it) {
		String annot_date = getDate();
		pruneBranch(node, annot_date, log_it);
	}

	public void pruneBranch(Bioentity node, String date, boolean log_it) {
		List<GeneAnnotation> purged_basket = new ArrayList<>();
		harvestPrunedBranch (node, purged_basket);

		List<GeneAnnotation> initial_annotations = node.getAnnotations();
		if (initial_annotations != null) {
			for (int i = initial_annotations.size() - 1; i >= 0; i--) {
				GeneAnnotation annotation = initial_annotations.get(i);
				if (!annotation.isMRC() && !annotation.isDirectNot()) {
					_removeAssociation(node, annotation.getCls());
				}
			}
		}
		if (log_it)
			LogAction.inst().logPruning(node, date, purged_basket);
	}

	private void harvestPrunedBranch(Bioentity node, List<GeneAnnotation> purged_basket) {
		/*
		 * Keep track of any associations that would need to be
		 * restored if the user changes their mind
		 */
		List<GeneAnnotation> initial_annotations = node.getAnnotations();
		if (initial_annotations != null) {
			for (int i = initial_annotations.size() - 1; i >= 0; i--) {
				GeneAnnotation annotation = initial_annotations.get(i);
				if (annotation.isMRC() || annotation.isDirectNot()) {
					GeneAnnotation removed = _removeAssociation(node, annotation.getCls());
					purged_basket.add(removed);
				}
			}
		}
		List<Bioentity> children = node.getChildren();
		if (children != null) {
			for (Bioentity child : children) {
				harvestPrunedBranch (child, purged_basket);
			}
		}
	}

	public void graftBranch(Family family, Bioentity node, List<GeneAnnotation> archive, boolean log) {
		restoreInheritedAssociations(family, node, null, null);
		List<GeneAnnotation> annots = node.getAnnotations();
		for (int i = annots.size() - 1; i > 0; i--) {
			GeneAnnotation annot = annots.get(i);
			removeMoreGeneralTermsFromNode(node, annot.getCls());			
		}
		if (archive != null) {
			for (GeneAnnotation archived_annot : archive) {
				boolean negate = archived_annot.isDirectNot();
				if (negate) {
					GeneAnnotation negate_assoc = null;
					annots = archived_annot.getBioentityObject().getAnnotations();
					for (int i = annots.size() - 1; i > 0 && negate_assoc == null; i--) {
						GeneAnnotation existing_annot = annots.get(i);
						if (existing_annot.getCls().equals(archived_annot.getCls())) {
							negate_assoc = existing_annot;
						}
					}
					if (negate_assoc != null) {
						setNot(family, archived_annot.getBioentityObject(), negate_assoc, archived_annot.getShortEvidence(), false, null);
					}
				} else {
					Bioentity top = archived_annot.getBioentityObject();
					String term = archived_annot.getCls();
					WithEvidence withs = new WithEvidence(family.getTree(), top, term);
					List<String> exp_withs = withs.getExpWiths();
					List<String> top_with = new ArrayList<> ();
					top_with.add(top.getId());
					int qualifiers = getGOqualifiers(archived_annot.getQualifiers());
					_restoreAssociation(top,
							term,
							qualifiers,
							family,
							family.getReference(),
							archived_annot.getLastUpdateDate(),
							negate,
							withs.regulates(),
							top_with,
							exp_withs);
				}
			}
		}
	}

	private boolean restoreInheritedAssociations(Family family, Bioentity node, String aspect, String negated_term) {
		/*
		 * First collect all of the ancestral annotations that should be applied to this node.
		 */
		List<GeneAnnotation> ancestral_assocs = new ArrayList<>();
		if (node.getParent() != null) {
			collectAncestorTerms(node.getParent(), negated_term, aspect, ancestral_assocs);
		}

		boolean restoration = false;
		for (GeneAnnotation ancestral_assoc : ancestral_assocs) {
			Bioentity top = ancestral_assoc.getBioentityObject();
			if (top.getPaintId() == null) {
				log.error("Got wrong bioentity " + top);
			}
			String term = ancestral_assoc.getCls();
			WithEvidence withs = new WithEvidence(family.getTree(), top, term);
			List<String> exp_withs = withs.getExpWiths();
			boolean negate = withs.isExperimentalNot();
			List<String> top_with = new ArrayList<> ();
			top_with.add(top.getId());
			int qualifiers = getGOqualifiers(ancestral_assoc.getQualifiers());
			_restoreAssociation(node,
					term,
					qualifiers,
					family,
					family.getReference(),
					ancestral_assoc.getLastUpdateDate(),
					negate,
					withs.regulates(),
					top_with,
					exp_withs);
			restoration = true;
		}
		return restoration;
	}

	private int getGOqualifiers(int current) {
		if (current > 0) {
			int qualifiers = GeneAnnotation.COLOCALIZES_MASK | GeneAnnotation.CONTRIBUTES_TO_MASK | GeneAnnotation.INTEGRAL_TO_MASK;
			qualifiers &= current;
			return qualifiers;
		} else {
			return current;
		}
	}

	private GeneAnnotation _restoreAssociation(Bioentity node,
			String go_id,
			int qualifiers,
			Family family,
			String reference,
			String date,
			boolean negate,
			List<GeneAnnotation> curator_inference,
			List<String> top_with,
			List<String> exp_withs) {
		GeneAnnotation top_assoc = null;
		/**
		 * Only proceed if this is not one of the original sources of information for this association
		 * and this node is not yet annotated to either this term
		 */
		if (!exp_withs.contains(node.getId()) && AnnotationUtil.isAnnotatedToTerm(node.getAnnotations(), go_id) == null) {
			GeneAnnotation assoc;
			if (top_with.contains(node.getId())) {
				assoc = createAnnotation(node, go_id, qualifiers, family, reference, date, true, negate, curator_inference, exp_withs);
				// not dirty if this is restoring annotations from a saved file
				//			DirtyIndicator.inst().dirtyGenes(date == null);
				top_assoc = assoc;
			} else {
				assoc = createAnnotation(node, go_id, qualifiers, family, reference, date, false, negate, curator_inference, top_with);
			}

			/*
			 * Doing this afterwards to avoid examining it in the above operation
			 */
			node.addAnnotation(assoc);

			/*
			 * propagate negation...
			 */
			assoc.setIsNegated(negate);

			/*
			 * Make the top ancestral gene in this branch of the gene family the source of information
			 */
			List<Bioentity> children = node.getChildren();
			if (children != null) {
				for (Bioentity child : children) {
					if (!child.isPruned()) {
						_restoreAssociation(child,
								go_id,
								qualifiers,
								family,
								reference,
								date,
								negate,
								curator_inference,
								top_with,
								exp_withs);
					}
				}
			}
		}
		return top_assoc;
	}

	private void collectAncestorTerms(Bioentity ancestral_node, 
			String exclude_term, 
			String aspect, 
			List<GeneAnnotation> ancestral_collection) {
		List<GeneAnnotation> ancestral_assocs = AnnotationUtil.getAspectPaintAssociations(ancestral_node, aspect);
		if (ancestral_assocs != null) {
			/*
			 * For each term
			 * If it is a direct annotation
			 * and
			 * If there are no current annotations to that term or any of its child terms
			 *
			 * Then an association to this term needs to be restored
			 */
			for (GeneAnnotation ancestral_assoc : ancestral_assocs) {
				// Did a curator annotate this ancestor?
				// And it isn't the term that has just been negated
				String ancestral_term = ancestral_assoc.getCls();
				if ((ancestral_assoc.isMRC() || ancestral_assoc.isDirectNot()) && !ancestral_term.equals(exclude_term)) {
					// Is a child term of this already in the list?
					// if yes then don't need to add it.
					boolean covered = false;
					for (GeneAnnotation check_assoc : ancestral_collection) {
						String check_term = check_assoc.getCls();
						// is first term/argument (from ancestral protein)
						// is a broader term for the second term/argument (from descendant protein)
						// then there is no need to re-associate the broader term.
						covered |= OWLutil.inst().moreSpecific(ancestral_term, check_term);
					}
					if (!covered) {
						ancestral_collection.add(ancestral_assoc);
					}
				}
			}
		}
		if (ancestral_node.getParent() != null) {
			collectAncestorTerms(ancestral_node.getParent(), exclude_term, aspect, ancestral_collection);
		}
	}

	public void undoAssociation(Family family, GeneAnnotation annot) {
		_removeAssociation(annot.getBioentityObject(), annot.getCls());
		restoreInheritedAssociations(family, annot.getBioentityObject(), annot.getAspect(), null);
	}


	private GeneAnnotation _removeAssociation(Bioentity node, String go_id) {
		GeneAnnotation removed = null;
		List<GeneAnnotation> current = node.getAnnotations();
		for (int i = 0; i < current.size() && removed == null; i++) {
			GeneAnnotation a = current.get(i);
			if (a.getCls().equals(go_id)) {
				if (AnnotationUtil.isPAINTAnnotation(a)) {
					removed = a;
				}
				else if (node.isLeaf()) {
					GafRecorder.inst().unquestioned(a);
				}
			}
		}
		current.remove(removed);

		List<Bioentity> children = node.getChildren();
		if (children != null) {
			for (Bioentity child : children) {
				_removeAssociation(child, go_id);
			}
		}

		return removed;
	}

	public void setNot(Family family, Bioentity node, GeneAnnotation assoc, String evi_code, boolean log_op, List<GeneAnnotation> removed) {
		if (!assoc.isNegated()) {
			assoc.setIsNegated(true);
			assoc.setDirectNot(true);
			assoc.setEvidence(evi_code, null);

			List<String> with_str = new ArrayList<>();
			/*
			If this NOT has been actively added by the user indicate the direct parent
			 */
			//	with_str.add(node.getParent().getId());

			/*
			Keep both the existing evidence, but now also add the negative evidence
			 */
			List<Bioentity> leafList = family.getTree().getLeafDescendants(node);
			for (Bioentity leaf : leafList) {
				List<GeneAnnotation> leafAssocs = AnnotationUtil.getAspectExpAssociations(leaf, assoc.getAspect());
				for (GeneAnnotation leafAssoc : leafAssocs) {
					if (leafAssoc.getCls().equals(assoc.getCls()) && leafAssoc.isNegated()) {
						with_str.add(leaf.getId());
					}
				}

			}
			if (with_str.isEmpty() && node.getParent() != null) {
				with_str.add(node.getParent().getId());
			}
			assoc.setWithInfos(with_str);

			/*
			 * Need to propagate this change to all descendants
			 */
			propagateNegationDown(node, assoc, true);

			restoreInheritedAssociations(family, assoc.getBioentityObject(), assoc.getAspect(), assoc.getCls());

			if (log_op)
				LogAction.inst().logNot(assoc, removed);
		}
	}

	public void unNot (GeneAnnotation assoc) {
		assoc.setDirectNot(false);
		assoc.setIsNegated(false);
		assoc.setEvidence(Constant.ANCESTRAL_EVIDENCE_CODE, null);
		String aspect = OWLutil.inst().getAspect(assoc.getCls());
		GeneAnnotation a = getAncestralNodeWithPositiveEvidenceForTerm(assoc.getBioentityObject().getParent(), assoc.getCls(), aspect);
		if (a != null) {
			Collection<String> withs = new ArrayList<>();
			withs.add(assoc.getBioentity());
			assoc.setWithInfos(withs);
		}
		propagateNegationDown(assoc.getBioentityObject(), assoc, false);

		removeMoreGeneralTerms(assoc.getBioentityObject(), assoc.getCls());	

		//			DirtyIndicator.inst().dirtyGenes(true);
	}

	private GeneAnnotation getAncestralNodeWithPositiveEvidenceForTerm(Bioentity node, String term, String aspect) {
		List<GeneAnnotation> node_assocs = AnnotationUtil.getAspectExpAssociations(node, aspect);
		if (node_assocs != null) {
			for (GeneAnnotation a : node_assocs) {
				if (a.getCls().equals(term) && !a.isNegated() && a.isMRC()) {
					return a;
				}
			}
		}
		if (node.getParent() == null) {
			return null;
		} else {
			return getAncestralNodeWithPositiveEvidenceForTerm(node.getParent(), term, aspect);
		}
	}

	private void propagateNegationDown(Bioentity node, GeneAnnotation assoc, boolean is_not) {
		List<Bioentity> children = node.getChildren();
		if (children == null)
			return;
		for (Bioentity child : children) {
			/*
			 * Better to see if the child term is_a (or is part_of) the parent term, rather than an exact match
			 */
			GeneAnnotation child_assoc = AnnotationUtil.isAnnotatedToTerm(child.getAnnotations(), assoc.getCls(), assoc.getAspect());
			if (child_assoc != null) {
				child_assoc.setIsNegated(is_not);
				child_assoc.setDirectNot(false);
				Collection<String> withs = new ArrayList<>();
				withs.add(assoc.getBioentity());
				child_assoc.setWithInfos(withs);
				child_assoc.setEvidence(Constant.ANCESTRAL_EVIDENCE_CODE, null);
				// all inherited annotations should have evidence code of "IBA", including
				// NOT annotations
			}
			propagateNegationDown(child, assoc, is_not);
		}
	}

	public boolean contradictoryNegation(Family family, GeneAnnotation assoc, List<GeneAnnotation> extant_assocs) {
		List<GeneAnnotation> dependent_ancestral_annots = new ArrayList<>();
		if (!extant_assocs.isEmpty()) {
			if (assoc.getWithInfos().size() == 1) {
				/*
				 * Find the ancestral annotation that this was inherited from
				 */
				String ancestral_node_id = assoc.getWithInfos().iterator().next();
				List<LogEntry> done_log = LogAction.inst().getDoneLog();
				for (LogEntry entry : done_log) {
					if (entry.getAction().equals(LOG_ENTRY_TYPE.ASSOC)) {
						GeneAnnotation logged_annot = entry.getLoggedAssociation();
						if (logged_annot.getBioentityObject().getId().equals(ancestral_node_id) &&
								logged_annot.getCls().equals(assoc.getCls())) {
							/* 
							 * Now see if the experimental evidence this ancestral annotation
							 * is based upon is found among the evidence that is being challenged.
							 */
							List<String> exp_withs = new ArrayList<>();
							exp_withs.addAll(logged_annot.getWithInfos());
							for (int i = exp_withs.size() - 1; i >= 0; i--) {
								String exp_id = exp_withs.get(i);
								for (GeneAnnotation leaf_annot : extant_assocs) {
									if (exp_id.equals(leaf_annot.getBioentityObject().getId())) {
										exp_withs.remove(leaf_annot.getBioentityObject().getId());
									}
								}
							}
							if (exp_withs.isEmpty()) {
								dependent_ancestral_annots.add(logged_annot);
								if (family != null) {
									LogAction.inst().undo(family, entry);
								}
							}
						}
					}
				}
			}
		}
		return !dependent_ancestral_annots.isEmpty();
	}

	public void undoChallenge(Family family, GeneAnnotation exp_annot, List<GeneAnnotation> removed) {
		GafRecorder.inst().acceptExperimental(exp_annot);
		AnnotationUtil.acceptExpAnnotation(exp_annot);

		for (GeneAnnotation restore_annot : removed) {
			LogAction.inst().redo(family, restore_annot);
		}
	}

	public List<GeneAnnotation> challengeExpAnnotation(Family family, List<GeneAnnotation> challenged_assocs, String rationale) {
		return 	challengeExpAnnotation(family,challenged_assocs, rationale, true);
	}

	public List<GeneAnnotation> challengeExpAnnotation(Family family, List<GeneAnnotation> challenged_assocs, String rationale, boolean is_new) {
		List<GeneAnnotation> dependent_annots = new ArrayList<>();
		GafRecorder.inst().recordChallengeInGAF(challenged_assocs, family, rationale, is_new);
		for (GeneAnnotation positive_annot : challenged_assocs) {
			Bioentity leaf = positive_annot.getBioentityObject();
			/*
			 * This is the most basic operation of the challenge
			 * simply removing this leaf node's annotation from 
			 * its list of experimental evidence 
			 * Thus, it can no longer be used for making phylogenetic inferences
			 */
			AnnotationUtil.removeExpAnnotation(leaf, positive_annot);
			/*
			 * May need to remove any annotations that were solely dependent on
			 * this annotation as evidence
			 */
			contradictoryNegation(family, positive_annot, dependent_annots);
		}
		return dependent_annots;
	}
}

