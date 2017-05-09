package org.bbop.phylo.gaf;
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


import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;
import org.bbop.phylo.annotate.AnnotationUtil;
import org.bbop.phylo.annotate.PaintAction;
import org.bbop.phylo.annotate.WithEvidence;
import org.bbop.phylo.gaf.parser.CommentListener;
import org.bbop.phylo.gaf.parser.GAFParser;
import org.bbop.phylo.gaf.parser.GafDocument;
import org.bbop.phylo.gaf.parser.GafObjectsBuilder;
import org.bbop.phylo.io.panther.IDmap;
import org.bbop.phylo.model.Bioentity;
import org.bbop.phylo.model.Family;
import org.bbop.phylo.model.GeneAnnotation;
import org.bbop.phylo.owl.OWLutil;
import org.bbop.phylo.tracking.LogAction;
import org.bbop.phylo.tracking.LogAlert;
import org.bbop.phylo.tracking.LogEntry;
import org.bbop.phylo.util.Constant;
import org.bbop.phylo.util.FileUtil;
import org.bbop.phylo.util.TimerUtil;

public class GafPropagator {

	protected static Logger log = Logger.getLogger(GafPropagator.class);

	/**
	 * Method declaration
	 *
	 * @param gafdoc gaf_file
	 * @throws IOException
	 * @see
	 */
	private static void propagate(GafDocument gafdoc, Family family) throws IOException {
		List<GeneAnnotation> gaf_annotations = gafdoc.getGeneAnnotations();

		Map<Bioentity, String> prune_dates = new HashMap<>();
		Map<Bioentity, List<GeneAnnotation>> negate_list = new HashMap<>();
		List<GeneAnnotation> clade_checklist = new ArrayList<>();

		IDmap mapper = IDmap.inst();

		for (GeneAnnotation gaf_annotation : gaf_annotations) {
			/*
			The GAF file has it's own instantiation of the protein nodes
			Need to be careful not to mix these up
			 */
			Bioentity gaf_node = gaf_annotation.getBioentityObject();
			/*
			 * Backwards compatibility
			 */
			if (gaf_annotation.getAssignedBy().equals(Constant.OLD_SOURCE))
				gaf_annotation.setAssignedBy(Constant.PAINT_AS_SOURCE);
			/*
			 * Similarly update the evidence codes
			 */
			String evi_code = gaf_annotation.getShortEvidence();
			if (evi_code.equals(Constant.OLD_ANCESTRAL_EVIDENCE_CODE)) {
				evi_code = Constant.ANCESTRAL_EVIDENCE_CODE;
				gaf_annotation.setEvidence(evi_code, null);
			} else if (evi_code.equals(Constant.OLD_DESCENDANT_EVIDENCE_CODE)) {
				evi_code = Constant.DESCENDANT_EVIDENCE_CODE;
				gaf_annotation.setEvidence(evi_code, null);
			}
			/*
			 * Next step is to find the corresponding gene node
			 */
			List<Bioentity> seqs;
			seqs = mapper.getGeneByDbId(gaf_node.getId());
			if (seqs == null) {
				seqs = mapper.getGenesBySeqId(gaf_node.getSeqDb(), gaf_node.getSeqId());
				if (seqs == null || seqs.size() == 0) {
					seqs = mapper.getGenesBySeqId("UniProtKB", gaf_node.getLocalId());
				}
			} 
			if (seqs == null) {
				log.debug("May be trouble");
				/*
				 * If a node can't be found it is likely not a big deal
				 * The only really important nodes are the ancestors from which everything else is propagated.
				 */
				if (!gaf_annotation.getShortEvidence().equals(Constant.ANCESTRAL_EVIDENCE_CODE)) {
					LogAlert.logMissing(gaf_node, gaf_annotation);
				} else if (gaf_annotation.isCut()){
					log.debug("Need to deal with this!!!!");
				}
			} else {
				int seq_count = 0;
				GeneAnnotation original = gaf_annotation;
				for (Bioentity seq_node : seqs) {
					if (seq_count > 0) {
						// clone the gaf annotation
						gaf_annotation = new GeneAnnotation(original);
					}
					gaf_annotation.setBioentityObject(seq_node);
					gaf_annotation.setBioentity(seq_node.getId());
					parseAnnotations(family, seq_node, gaf_annotation, prune_dates, negate_list, clade_checklist);
					seq_count++;
				}
			} // end for loop going through gaf file contents
		}
		Set<Bioentity> pruned = prune_dates.keySet();
		for (Bioentity node : pruned) {
			node.setPrune(true);
			PaintAction.inst().pruneBranch(node, prune_dates.get(node), true);
		}

		if (!negate_list.isEmpty()) {
			applyNots(family, negate_list);
		}
		if (!clade_checklist.isEmpty()) {
			cladeCheck(family, clade_checklist);
		}
	}

	private static void parseAnnotations(Family family,
			Bioentity node,
			GeneAnnotation gaf_annotation,
			Map<Bioentity, String> prune_dates,
			Map<Bioentity, List<GeneAnnotation>> negate_list,
			List<GeneAnnotation> clade_checklist) {

		if (gaf_annotation.isCut()) {
			prune_dates.put(node, gaf_annotation.getLastUpdateDate());
		}
		/*
		 * Ignore the rows (from older GAFs) that are for descendant nodes 
		 * in the tree. These will be propagated from the ancestral nodes
		 * that were directly annotated
		 */
		else {
			String evi_code = gaf_annotation.getShortEvidence();

			if (!evi_code.equals(Constant.ANCESTRAL_EVIDENCE_CODE)) {
				List<String> go_ids = AnnotationUtil.getLatestGOID(node, gaf_annotation);
				for (String go_id : go_ids) {
					if (gaf_annotation.isNegated()) {
						List<GeneAnnotation> not_annots = negate_list.get(node);
						if (not_annots == null) {
							not_annots = new ArrayList<>();
							negate_list.put(node, not_annots);
						}
						// update the go-id in case the GAF contains an obsolete ID
						gaf_annotation.setCls(go_id);
						not_annots.add(gaf_annotation);
					} else {
						if (AnnotationUtil.isAnnotatedToTerm(node.getAnnotations(), go_id, gaf_annotation.getAspect()) == null) {
							LogEntry.LOG_ENTRY_TYPE invalid = PaintAction.inst().isValidTerm(go_id, node, family.getTree());
							if (invalid == null) {
								WithEvidence withs = new WithEvidence(family.getTree(), node, go_id);
								GeneAnnotation assoc = PaintAction.inst().propagateAssociation(family, node, go_id, withs, gaf_annotation.getLastUpdateDate(), gaf_annotation.getQualifiers());
								clade_checklist.add(assoc);
							} else {
								LogAlert.logInvalid(node, gaf_annotation, invalid);
							}
						}
					}
				}
			}
		}
	}

	public static boolean importAnnotations(Family family, File family_dir) {
		boolean ok = FileUtil.validPath(family_dir);
		TimerUtil timer = new TimerUtil();
		if (ok) {
			File gaf_file = new File(family_dir, family.getFamily_name() + Constant.GAF_SUFFIX);
			GafObjectsBuilder builder = new GafObjectsBuilder();
			GafDocument gafdoc;
			try {
				log.info("Propagating GAF annotations");
				String full_name = gaf_file.getAbsolutePath();
				gafdoc = builder.buildDocument(full_name);
				family.setGafComments(gafdoc.getComments());
				propagate(gafdoc, family);
			} catch (IOException | URISyntaxException e) {
				log.warn("URI Syntax exception for " + family.getFamily_name());
				ok = false;
			}
			log.info("Propagation for " + family.getFamily_name() + " took " + timer.reportElapsedTime());
		} else {
			log.error("GAF directory is invalid: " + family_dir);
		}
		return ok;
	}

	private static void applyNots(Family family, Map<Bioentity, List<GeneAnnotation>> negate_list) {
		/*
        Leaf annotation were also added to the list and these will be redundant if the
        direct NOT is to ancestral node.
        These need to be removed before processing the NOT
		 */

		/*
        For each protein node that had one or more NOT qualifiers in the GAF files
		 */
		List<Bioentity> skip_list = new ArrayList<>();
		for (Bioentity node : negate_list.keySet()) {
			if (AnnotationUtil.isAncestralNode(node)) {
				/*
                Remove any annotations to descendants
				 */
				List<Bioentity> leaves = family.getTree().getLeafDescendants(node);
				List<GeneAnnotation> ancestral_negations = negate_list.get(node);
				for (Bioentity leaf : leaves) {
					for (GeneAnnotation ancestral_negation : ancestral_negations) {
						/*
                    If this descendant is negated check to see if it is the same GO term
						 */
						if (negate_list.containsKey(leaf)) {
							List<GeneAnnotation> leaf_negations = negate_list.get(leaf);
							for (int i = leaf_negations.size() - 1; i >= 0; i--) {
								GeneAnnotation leaf_negation = leaf_negations.get(i);
								if (ancestral_negation.getCls().equals(leaf_negation.getCls())) {
									/*
                                redundant, the ancestral negation will produce this
                                remove it from the actionable list
									 */
									leaf_negations.remove(i);
									if (leaf_negations.isEmpty()) {
										skip_list.add(leaf);
									}
								}
							}
						}
					}
				}
			}
		}

		for (Bioentity skip : skip_list) {
			negate_list.remove(skip);
		}

		OWLutil owl = OWLutil.inst();
		for (Bioentity node : negate_list.keySet()) {
			for (GeneAnnotation notted_gaf_annot : negate_list.get(node)) {
				/*
				 * Need to propagate this change to all descendants
				 */
				List<GeneAnnotation> associations = new ArrayList<>();
				associations.addAll(node.getAnnotations());
				if (associations != null) {
					for (GeneAnnotation assoc : associations) {
						boolean match = AnnotationUtil.isPAINTAnnotation(assoc);
						if (match) {
							match = assoc.getCls().equals(notted_gaf_annot.getCls());
							if (!match) {
								match &= owl.moreSpecific(notted_gaf_annot.getCls(), assoc.getCls());
								if (match) {
									log.info("negating subclass for " + notted_gaf_annot);
								}
							}
							if (match) {
								List<String> all_evidence = assoc.getReferenceIds();
								/*
								 * Should just be one piece of evidence
								 */
								if (all_evidence.size() == 1) {
									String eco = notted_gaf_annot.getShortEvidence();
									if (eco.equals("LOF")) {
										eco = Constant.LOSS_OF_FUNCTION;
									}
									if (!eco.equals(Constant.KEY_RESIDUES_EC) &&
											!eco.equals(Constant.DIVERGENT_EC) &&
											!eco.equals(Constant.LOSS_OF_FUNCTION)) {
										log.error("Bad ECO in " + notted_gaf_annot);
										eco = Constant.DIVERGENT_EC;
									}
									PaintAction.inst().setNot(family, node, assoc, eco, true, null);
								} else {
									log.info("Didn't set NOT for " + notted_gaf_annot);
								}
							}
						}
					}
				}
			}
		}
	}

	private static void cladeCheck(Family family, List<GeneAnnotation> clade_checklist) {
		for (GeneAnnotation assoc : clade_checklist) {
			Bioentity node = assoc.getBioentityObject();
			if (!assoc.isNegated()) {
				PaintAction.inst().filterOutLosses(family, node, assoc);
			}
		}
	}

	public static boolean importChallenges(Family family, File family_dir) {
		boolean ok = FileUtil.validPath(family_dir);
		boolean challenges_found = false;
		if (ok) {
			File gaf_file = new File(family_dir, family.getFamily_name() + Constant.CHALLENGED_SUFFIX);
			if (gaf_file.exists() && gaf_file.canRead()) {
				GafObjectsBuilder builder = new GafObjectsBuilder();
				GAFParser parser = builder.getParser();
				final List<String> rationales = new ArrayList<>();
				try {
					log.info("building disputed GAF document");
					String full_name = gaf_file.getAbsolutePath();

					parser.addCommentListener(new CommentListener() {

						@Override
						public void readingComment(String comment, String line, int lineNumber) {
							if (comment.contains("Disputed")) {
								rationales.add(comment);
							}
						}
					});

					GafDocument gafdoc = builder.buildDocument(full_name);
					//					family.setGafComments(gafdoc.getComments());
					challenges_found = eliminate(gafdoc, family, rationales);
				} catch (IOException | URISyntaxException e) {
					ok = false;
				}
			}
		} else {
			log.error("GAF directory is invalid: " + family_dir);
		}
		return challenges_found;
	}

	private static boolean eliminate(GafDocument gafdoc, Family family, List<String> rationales) throws IOException {
		List<GeneAnnotation> challenged_annotations = gafdoc.getGeneAnnotations();

		int index = 0;
		IDmap mapper = IDmap.inst();
		for (GeneAnnotation positive_annot : challenged_annotations) {
			List<GeneAnnotation> positive = new ArrayList<>();
			/*
			 * Next step is to find the corresponding annotation that was previously loaded 
			 * (not just this malloc, but the active one in use)
			 */
			List<Bioentity> seqs;
			Bioentity gaf_node = positive_annot.getBioentityObject();
			seqs = mapper.getGeneByDbId(gaf_node.getId());
			if (seqs == null) {
				seqs = mapper.getGenesBySeqId(gaf_node.getSeqDb(), gaf_node.getSeqId());
				if (seqs == null || seqs.size() == 0) {
					seqs = mapper.getGenesBySeqId("UniProtKB", gaf_node.getLocalId());
				}
			} 
			for (Bioentity node : seqs) {
				List<GeneAnnotation> node_annots = node.getAnnotations();
				boolean found = false;
				for (int i = 0; i < node_annots.size() && !found; i++) {
					GeneAnnotation node_annot = node_annots.get(i);
					if (node_annot.getCls().equals(positive_annot.getCls()) &&
							node_annot.getShortEvidence().equals(positive_annot.getShortEvidence()) &&
									node_annot.getReferenceIds().get(0).equals(positive_annot.getReferenceIds().get(0))) {
						// sure as hell hope this is it
						found = true;
						positive.add(node_annot);
						String full_rationale = rationales.get(index);
						List<GeneAnnotation> removed = 	PaintAction.inst().challengeExpAnnotation(family, positive, full_rationale, false);
						LogAction.inst().logChallenge(node_annot, removed, full_rationale);
					}
				}
			}
		}
		return !challenged_annotations.isEmpty();
	}

}
