package org.bbop.phylo.gaf;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.io.IOUtils;
import org.apache.log4j.Logger;
import org.bbop.phylo.annotate.AnnotationUtil;
import org.bbop.phylo.annotate.WithEvidence;
import org.bbop.phylo.config.TouchupConfig;
import org.bbop.phylo.gaf.parser.GafDocument;
import org.bbop.phylo.gaf.parser.GafWriter;
import org.bbop.phylo.io.panther.IDmap;
import org.bbop.phylo.io.panther.ParsingHack;
import org.bbop.phylo.model.Bioentity;
import org.bbop.phylo.model.Family;
import org.bbop.phylo.model.GeneAnnotation;
import org.bbop.phylo.model.Tree;
import org.bbop.phylo.tracking.LogAction;
import org.bbop.phylo.tracking.LogEntry;
import org.bbop.phylo.tracking.LogUtil;
import org.bbop.phylo.util.Constant;
import org.bbop.phylo.util.FileUtil;
import org.bbop.phylo.util.TimerUtil;

public class GafRecorder {

	private static final Logger log = Logger.getLogger(GafRecorder.class);

	private static GafRecorder INSTANCE;

	private GafDocument questioned_annots;
	private Map<GeneAnnotation, String> challenged_annots;

	private GafRecorder() {
	}

	public static GafRecorder inst() {
		if (INSTANCE == null) {
			INSTANCE = new GafRecorder();
		}
		return INSTANCE;
	}

	public void clearChallenges() {
		questioned_annots = null;
		challenged_annots = null;
	}

	public void record(Family family, File family_dir, String comment) {
		String family_name = family.getFamily_name();
		boolean ok = FileUtil.validPath(family_dir);
		TimerUtil timer = new TimerUtil();
		if (ok) {
			log.info("Saving annotations to GAF");
			File gaf_file = new File(family_dir, family_name + Constant.GAF_SUFFIX);
			Tree tree = family.getTree();
			GafDocument gaf_doc = new GafDocument(gaf_file.getAbsolutePath(), family_dir.getAbsolutePath());
			addComments(family, comment, gaf_doc);
			Map<Bioentity, String> originalIDs = new HashMap<>();
			addAnnotations(family, tree, tree.getRoot(), gaf_doc, originalIDs);
			GafWriter gaf_writer = new GafWriter();
			gaf_writer.setStream(gaf_file);
			gaf_writer.write(gaf_doc);
			IOUtils.closeQuietly(gaf_writer);
			Set<Bioentity> modified = originalIDs.keySet();
			for (Bioentity modified_node : modified) {
				String originalID = originalIDs.get(modified_node);
				// restore it
				modified_node.setId(originalID);
				modified_node.setDb(originalID.substring(0, originalID.indexOf(':')));
				List<GeneAnnotation> annotations = modified_node.getAnnotations();
				if (annotations != null) {
					for (GeneAnnotation annotation : annotations) {
						annotation.setBioentity(modified_node.getId());
					}
				}
			}

			if (questioned_annots != null && !questioned_annots.getGeneAnnotations().isEmpty()) {
				File challenge_file = new File(family_dir, family_name + Constant.QUESTIONED_SUFFIX);
				GafWriter challenge_writer = new GafWriter();
				gaf_writer.setStream(challenge_file);
				gaf_writer.write(questioned_annots);
				IOUtils.closeQuietly(challenge_writer);
			}
			if (challenged_annots != null && !challenged_annots.isEmpty()) {
				File challenge_file = new File(family_dir, family_name + Constant.CHALLENGED_SUFFIX);
				GafDocument gaf = new GafDocument(gaf_file.getAbsolutePath(), family_dir.getAbsolutePath());
				GafWriter challenge_writer = new GafWriter();
				Set<GeneAnnotation> disputed = challenged_annots.keySet();
				for (GeneAnnotation dispute : disputed) {
					gaf.addComment(challenged_annots.get(dispute));
					gaf.addGeneAnnotation(dispute);
				}
				gaf_writer.setStream(challenge_file);
				gaf_writer.write(gaf);
				IOUtils.closeQuietly(challenge_writer);
			}
			log.info("Wrote updated paint GAF in " + timer.reportElapsedTime() + " to " + gaf_file);
		} else {
			log.error("Unable to save paint GAF for " + family_name + " in " + family_dir);
		}
	}

	public void experimental(Family family, File family_dir, String comment) {
		String family_name = family.getFamily_name();
		boolean ok = FileUtil.validPath(family_dir);
		if (ok) {
			File gaf_file = new File(family_dir, family_name + Constant.EXP_SUFFIX);
			Tree tree = family.getTree();
			GafDocument gaf_doc = new GafDocument(gaf_file.getAbsolutePath(), family_dir.getAbsolutePath());
			addComments(family, comment, gaf_doc);
			addExpAnnotations(family, tree.getLeaves(), gaf_doc);
			GafWriter gaf_writer = new GafWriter();
			gaf_writer.setStream(gaf_file);
			gaf_writer.write(gaf_doc);
			IOUtils.closeQuietly(gaf_writer);
		} else {
			log.error("Unable to save experimental evidence GAF for " + family_name + " in " + family_dir);
		}		
	}

	private void addAnnotations(Family family, Tree tree, Bioentity node, GafDocument gaf_doc, Map<Bioentity, String> originalIDs) {
		if (node.isPruned()) {
			/* Write out one row to record the pruned branch */
			GeneAnnotation stump = createStump(family, node);
			gaf_doc.addGeneAnnotation(stump);
		}
		else {
			List<GeneAnnotation> annotations = node.getAnnotations();
			// For testing only, delete later
			if (node.getDb() == null) {
				node.setDb(Constant.PANTHER_DB);
				node.setId(Constant.PANTHER_DB + ":" + node.getPaintId());
			}
			boolean use_seq = ParsingHack.useUniProtID(node.getDb());
			if (annotations != null) {
				for (GeneAnnotation annotation : annotations) {
					/**
					 * Only save those associations made within the context of PAINT
					 */
					boolean include = AnnotationUtil.isPAINTAnnotation(annotation);
					include &= annotation.isMRC() || node.isLeaf() || annotation.isDirectNot();
					if (include) {
						if (node.isLeaf()) {
							// This is logically not needed, but is a convenience for PanTree
							addExpWith(tree, node, annotation);
							if (use_seq) {
								originalIDs.put(node, node.getId());
								node.setId(node.getSeqDb() + ':' + node.getSeqId());
								node.setDb(node.getSeqDb());
								annotation.setBioentity(node.getSeqDb() + ':' + node.getSeqId());
							}
							if (node.getSymbol() == null || node.getSymbol().trim().length() == 0) {
								log.info("Missing a symbol for " + node.getId());
								node.setSymbol(node.getSeqId());
							}
						}
						if (annotation.getWithInfos().size() == 0) {
							log.error("No with information for\n\t" + annotation);
						} // else {
						gaf_doc.addGeneAnnotation(annotation);
						//	}
					}
				}
			}
			/*
			 * And all the children as well, if this branch hasn't been pruned
			 */
			if (!node.isPruned()) {
				List<Bioentity> children = node.getChildren();
				if (children != null) {
					for (Bioentity child : children) {
						addAnnotations(family, tree, child, gaf_doc, originalIDs);
					}
				}
			}
		}
	}

	private void addExpWith(Tree tree, Bioentity node, GeneAnnotation annotation) {
		List<String> withs = new ArrayList<>();
		String ancestor_id = annotation.getWithInfos().iterator().next();
		withs.add(ancestor_id);

		/*
		 * Seems to just be the one ancestral node, so proceed
		 * First indicate the ancestral node
		 */

		/*
		 * Then add the ancestor's withs to feed back to PANTREE
		 */
		List<String> exp_withs;
		List<Bioentity> ancestor = IDmap.inst().getGeneByDbId(ancestor_id);
		if (ancestor != null) {
			if (ancestor.size() > 1) {
				log.debug("More than one ancestor? " + ancestor_id);
			}
			for (Bioentity a : ancestor) {
				WithEvidence evidence = new WithEvidence(tree, a, annotation.getCls());
				exp_withs = evidence.getExpWiths();
				withs.addAll(exp_withs);
			}
		} else {
			log.error("Where is the ancestral node for " + node + " to inherit " + annotation.getCls() + '?');
		}
		annotation.setWithInfos(withs);
	}

	private GeneAnnotation createStump(Family family, Bioentity node) {
		GeneAnnotation stump = new GeneAnnotation();
		stump.setBioentity(node.getId());
		stump.setBioentityObject(node);
		stump.setIsCut(true);
		stump.addReferenceId(family.getReference());
		stump.setAssignedBy(Constant.PAINT_AS_SOURCE);
		LogEntry log_entry = LogAction.inst().findEntry(node, null, LogEntry.LOG_ENTRY_TYPE.PRUNE);
		String date = log_entry.getDate();
		stump.setLastUpdateDate(date);
		return stump;
	}

	private void addComments(Family family, String comment, GafDocument gaf_doc) {
		List<String> comments = family.getGafComments();
		if (comments != null) {
			for (String comment_line : comments) {
				gaf_doc.addComment(comment_line);
			}
		}
		gaf_doc.addComment(comment);
	}

	private void addExpAnnotations(Family family, List<Bioentity> nodes, GafDocument gaf_doc) {
		for (Bioentity node : nodes) {
			List<GeneAnnotation> annotations = AnnotationUtil.getExperimentalAssociations(node);
			if (annotations != null && !annotations.isEmpty()) {
				for (GeneAnnotation annotation : annotations) {
					/**
					 * Only save those associations made within the context of PAINT
					 */
					gaf_doc.addGeneAnnotation(annotation);
				}
			}
		}
	}

	public void recordQuestionedAnnotationInGAF(List<GeneAnnotation> questioned, Family family) {
		String suffix = Constant.QUESTIONED_SUFFIX;
		String comment = "Regulation of annotation(s) questioned by: ";
		questioned_annots = questioned(questioned_annots, questioned, family, suffix, comment, null);
	}

	public void recordChallengeInGAF(List<GeneAnnotation> challenges, Family family, String rationale, boolean is_new) {
		if (challenged_annots == null) {
			challenged_annots = new HashMap<>();
		}
		for (GeneAnnotation dispute : challenges) {
			if (challenged_annots.get(dispute) == null) {
				String full_rationale = is_new ?
						"Disputed by " + System.getProperty("user.name") + " on " + LogUtil.dateNow() + 
						" -- " + dispute.getBioentityObject().getId() + " should not be annotated to " + dispute.getCls() + 
						" because " + rationale :
							rationale;
				challenged_annots.put(dispute, full_rationale);
			}
		}
	}

	private GafDocument questioned(GafDocument gaf, List<GeneAnnotation> challenges, Family family, 
			String suffix, String comment, String rationale) {
		boolean not_redundant = true;
		if (gaf == null) {
			File family_dir = new File(TouchupConfig.inst().gafdir);
			File gaf_file = new File(family_dir, family.getFamily_name() + suffix);
			gaf = new GafDocument(gaf_file.getAbsolutePath(), family_dir.getAbsolutePath());
		}
		for (GeneAnnotation challenge : challenges) {
			for (GeneAnnotation annot : gaf.getGeneAnnotations()) {
				not_redundant &= annot != challenge;
			}
			if (not_redundant) {
				gaf.addGeneAnnotation(challenge);
				gaf.addComment(comment + System.getProperty("user.name") + " on " + LogUtil.dateNow());
				if (rationale != null) {
					gaf.addComment(rationale);
				}
			}
		}
		return gaf;		
	}

	public void unquestioned(GeneAnnotation annot) {
		if (questioned_annots != null) {
			questioned_annots.getGeneAnnotations().remove(annot);
		}
	}
	
	public void acceptExperimental(GeneAnnotation annot) {
		if (challenged_annots != null) {
			challenged_annots.remove(annot);
		}
	}
}
