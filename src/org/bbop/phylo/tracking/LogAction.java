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

package org.bbop.phylo.tracking;

import java.util.ArrayList;
import java.util.List;

import org.bbop.phylo.annotate.PaintAction;
import org.bbop.phylo.model.Bioentity;
import org.bbop.phylo.model.Family;
import org.bbop.phylo.model.GeneAnnotation;
import org.bbop.phylo.owl.OWLutil;
import org.bbop.phylo.tracking.LogEntry.LOG_ENTRY_TYPE;
import org.bbop.phylo.util.Constant;

public class LogAction {

	private static final org.apache.log4j.Logger logger = org.apache.log4j.Logger.getLogger(LogAction.class);

	private List<LogEntry> done_log;
	private List<LogEntry> undone_log;

	private static LogAction INSTANCE;

	private LogAction() {
	}

	public static LogAction inst() {
		if (INSTANCE == null) {
			INSTANCE = new LogAction();
		}
		return INSTANCE;
	}

	/*
	 * Separated into sections by aspect ?
	 * Include dates?
	 * Section for References
	 * 	http://en.wikipedia.org/wiki/SKI_protein
	 * 	PMID: 19114989 
	 * Phylogeny
	 * 	Two main clades, SKOR and SKI/SKIL, plus an outlier from Tetrahymena which aligns poorly, so I have not annotated AN0.

	 * Propagate GO:0004647 "phosphoserine phosphatase activity" to AN1 and GO:0016791 "phosphatase activity" to AN0.
	 * -Propagate "cytoplasm" to AN1 based on 3 annotations.
	 * -Propagate "chloroplast" to plants/chlamy.
	 * 
	 * Need to also log all NOTs
	 * 
	 * Challenge mechanism
	 * 	
	 */
	public void clearLog() {
		if (done_log == null) {
			done_log = new ArrayList<>();
		} else {
			done_log.clear();
		}
		if (undone_log == null) {
			undone_log = new ArrayList<>();
		} else {
			undone_log.clear();
		}
	}

	public void logAssociation(Bioentity node, GeneAnnotation assoc) {
		LogEntry entry = new LogEntry(node, assoc, LOG_ENTRY_TYPE.ASSOC, null);
		done_log.add(entry);
	}

	public void logNot(GeneAnnotation annotation, List<GeneAnnotation> removed) {
		LogEntry entry = new LogEntry(annotation.getBioentityObject(), annotation, LOG_ENTRY_TYPE.NOT, removed);
		done_log.add(entry);
	}

	public void logPruning(Bioentity node, String date, List<GeneAnnotation> purged) {
		LogEntry branch = findEntry(node, null, LogEntry.LOG_ENTRY_TYPE.PRUNE);
		if (branch != null) {
			done_log.remove(branch);
			undone_log.add(branch);
		} else {
			branch = new LogEntry(node, null, LOG_ENTRY_TYPE.PRUNE, purged);
			done_log.add(branch);
		}
	}

	public void logGrafting(Family family, Bioentity node) {
		LogEntry branch = findEntry(node, null, LogEntry.LOG_ENTRY_TYPE.PRUNE);
		if (branch != null) {
			done_log.remove(branch);
			PaintAction.inst().graftBranch(family, node, branch.getRemovedAssociations(), false);
			undone_log.add(branch);
		}
	}

	public LogEntry undo(Family family, GeneAnnotation assoc) {
		LogEntry entry = null;
		for (int i = 0; i < done_log.size() && entry  == null; i++) {
			LogEntry check = done_log.get(i);
			if (check.getNode().equals(assoc.getBioentityObject()) &&
					check.getTerm().equals(assoc.getCls()))
				entry = check;
		}
		return undo(family, entry);
	}

	public LogEntry undo(Family family) {
		LogEntry entry = null;
		int index = done_log.size() - 1;
		if (index >= 0) {
			entry = undo(family, done_log.get(index));
		}
		return entry;
	}

	public LogEntry undo (Family family, LogEntry entry) {
		done_log.remove(entry);
		takeAction(family, entry, true);
		undone_log.add(entry);
		return entry;
	}

	public LogEntry redo(Family family, GeneAnnotation assoc) {
		LogEntry entry = null;
		for (int i = 0; i < undone_log.size() && entry  == null; i++) {
			LogEntry check = undone_log.get(i);
			if (check.getNode().equals(assoc.getBioentityObject()) &&
					check.getTerm().equals(assoc.getCls()))
				entry = check;
		}
		return redo(family, entry);
	}

	public LogEntry redo(Family family) {
		LogEntry entry = null;
		int index = undone_log.size() - 1;
		if (index >= 0) {
			entry = redo(family, undone_log.get(index));
		}
		return entry;
	}

	public LogEntry redo(Family family, LogEntry entry) {
		undone_log.remove(entry);
		takeAction(family, entry, false);
		done_log.add(entry);
		return entry;
	}

	public void report(List<String> contents) {
		int pruned = logCount(LOG_ENTRY_TYPE.PRUNE);
		int challenged = logCount(LOG_ENTRY_TYPE.CHALLENGE);

		if (done_log != null) {
			contents.add(Logger.MF_SECTION);
			reportMF(contents, Constant.MF);
			contents.add(Logger.CC_SECTION);
			reportCC(contents, Constant.CC);
			contents.add(Logger.BP_SECTION);
			reportBP(contents, Constant.BP);
			if (pruned > 0) {
				contents.add(contents.size() - pruned, Logger.PRUNED_SECTION);
				reportEntries(done_log, contents, LOG_ENTRY_TYPE.PRUNE);
			}
			if (challenged > 0) {
				contents.add(contents.size() - challenged, Logger.CHALLENGED_SECTION);
				reportEntries(done_log, contents, LOG_ENTRY_TYPE.CHALLENGE);
			}

		}
	}

	public void reportMF(List<String> contents, String aspect) {
		for (LogEntry entry : done_log) {
			reportAspect(entry, contents, aspect, " has function ", " has LOST/MODIFIED function ");
		}
		contents.add("");
	}

	public void reportCC(List<String> contents, String aspect) {
		for (LogEntry entry : done_log) {
			reportAspect(entry, contents, aspect, " is found in ", " is NOT found in ");
		}
		contents.add("");
	}

	public void reportBP(List<String> contents, String aspect) {
		for (LogEntry entry : done_log) {
			reportAspect(entry, contents, aspect, " participates in ", " does NOT participate in ");
		}
		contents.add("");
	}

	public void reportEntries(List<String> contents, LOG_ENTRY_TYPE entry_type) {
		reportEntries(done_log, contents, entry_type);
	}

	public void reportEntries(List<LogEntry> log, List<String> contents, LOG_ENTRY_TYPE entry_type) {
		int entry_count = 0;
		for (LogEntry entry : log) {
			if (entry.getAction() == entry_type) {
				entry_count++;
				reportEntry(entry, contents);
			}
		}
		if (entry_count > 0)
			contents.add("");
	}

	private static void reportEntry(LogEntry entry, List<String> contents) {
		String comment = "";
		if (entry.getAction().equals(LOG_ENTRY_TYPE.CHALLENGE)) {
			GeneAnnotation assoc = entry.getLoggedAssociation();
			comment = " annotation to " +
					OWLutil.inst().getTermLabel(assoc.getCls()) +
					" (" + assoc.getCls() + ") from " + 
					assoc.getReferenceIds().toString() +
					" was challenged";
		} else {
			comment = " has been pruned from tree";
		}
		contents.add(entry.getDate() + ": " +
				Logger.makeLabel(entry.getNode())
		+ comment);		
	}

	private int logCount(LOG_ENTRY_TYPE entry_type) {
		int count = 0;
		for (LogEntry entry : done_log) {
			if (entry.getAction() == entry_type) {
				count++;
			}
		}
		return count;
	}

	private void reportAspect(LogEntry entry,
			List<String> contents,
			String aspect,
			String syntax_candy_4has,
			String syntax_candy_4not) {
		GeneAnnotation annotation = entry.getLoggedAssociation();
		if (annotation != null && annotation.getAspect().equals(aspect)) {
			switch (entry.getAction()) {
			case ASSOC: {
				if (annotation.isContributesTo()) {
					syntax_candy_4has = syntax_candy_4has.replace("has", "contributes to");
				}
				if (annotation.isColocatesWith()) {
					syntax_candy_4has = " co-localizes with ";
				}
				if (annotation.isIntegralTo()) {
					syntax_candy_4has = syntax_candy_4has.replace("has", "is integral to");
				}
				contents.add(annotation.getLastUpdateDate() + ": " +
						Logger.makeLabel(entry.getNode()) +
						(annotation.isDirectNot() ? syntax_candy_4not : syntax_candy_4has) +
						OWLutil.inst().getTermLabel(annotation.getCls()) +
						" (" + annotation.getCls() + ") ");
				break;
			}
			case NOT: {
				contents.add(annotation.getLastUpdateDate() + ": " +
						Logger.makeLabel(entry.getNode()) +
						syntax_candy_4not +
						OWLutil.inst().getTermLabel(annotation.getCls()) +
						" (" + annotation.getCls() + ") ");
				break;
			}
			case CHALLENGE: {
				contents.add(annotation.getLastUpdateDate() + ": " +
						Logger.makeLabel(entry.getNode()) + " to " +
						OWLutil.inst().getTermLabel(annotation.getCls()) +
						" (" + annotation.getCls() + ") " +
						" was challenged because " + entry.getRationale());
				break;
			}
			default:
				logger.info("Not logging " + entry.getNode());
				break;
			}
		}
	}

	private void takeAction(Family family, LogEntry entry, boolean undo) {
		PaintAction dab = PaintAction.inst();
		switch (entry.getAction()) {
		case ASSOC: {
			if (undo) {
				dab.undoAssociation(family, entry.getLoggedAssociation());
			} else {
				dab.propagateAssociation(family, entry.getLoggedAssociation());
			}
			break;
		}
		case NOT: {
			if (undo) {
				List<GeneAnnotation> restore_list = entry.getRemovedAssociations();
				if (restore_list != null) {
					for (GeneAnnotation restore : restore_list) {
						dab.restoreExpAssociation(family, restore);
					}
				}
				dab.unNot(entry.getLoggedAssociation());
			} else {
				List<GeneAnnotation> restore_list = entry.getRemovedAssociations();
				if (restore_list != null && !restore_list.isEmpty()) {
					dab.challengeExpAnnotation(family, restore_list, entry.getRationale());
				}
				dab.setNot(family, 
						entry.getNode(), 
						entry.getLoggedAssociation(), 
						entry.getLoggedAssociation().getShortEvidence(), 
						false, 
						restore_list);
			}
			break;
		}
		case PRUNE: {
			entry.getNode().setPrune(!entry.getNode().isPruned());
			if (undo) {
				dab.graftBranch(family, entry.getNode(), entry.getRemovedAssociations(), false);
			} else {
				dab.pruneBranch(entry.getNode(), false);
			}
			break;
		}
		case CHALLENGE: {
			if (undo) {
				dab.undoChallenge(family, entry.getLoggedAssociation(), entry.getRemovedAssociations());
			} else {
				List<GeneAnnotation> challenges = new ArrayList<>();
				challenges.add(entry.getLoggedAssociation());
				dab.challengeExpAnnotation(family, challenges, entry.getRationale());
			}
			break;
		}
		default:
			break;
		}
	}

	public LogEntry findEntry(Bioentity node, String go_id, LogEntry.LOG_ENTRY_TYPE action) {
		LogEntry found = null;
		for (LogEntry entry : done_log) {
			if (found == null) {
				if (entry.getNode() == node && ((go_id != null && entry.getTerm().equals(go_id) && action == entry.getAction())
						|| (go_id == null && action == entry.getAction())))
					found = entry;
			}
		}
		return found;
	}

	public String doneString() {
		return actionString(done_log);
	}

	public String undoneString() {
		return actionString(undone_log);
	}

	private String actionString(List<LogEntry> log) {
		if (log.size() > 0) {
			List<String> contents = new ArrayList<String>();
			int index = log.size() - 1;
			LogEntry entry = log.get(index);
			GeneAnnotation assoc = entry.getLoggedAssociation();
			if (assoc != null) {
				if (entry.getAction().equals(LOG_ENTRY_TYPE.ASSOC) ||
						entry.getAction().equals(LOG_ENTRY_TYPE.NOT)) {
					String aspect = assoc.getAspect();
					if (aspect.equals(Constant.MF)) {
						reportAspect(entry, contents, aspect, " has function ", " has lost/modified function ");
					} else if (aspect.equals(Constant.CC)) {
						reportAspect(entry, contents, aspect, " is found in ", " is not found in ");
					} if (aspect.equals(Constant.BP)) {
						reportAspect(entry, contents, aspect, " participates in ", " does not participate in ");
					}
				} else if (entry.getAction().equals(LOG_ENTRY_TYPE.CHALLENGE)) {
					reportEntries(log, contents, LOG_ENTRY_TYPE.CHALLENGE);
				}
			} else { // Pruning/grafting
				reportEntries(log, contents, LOG_ENTRY_TYPE.PRUNE);
			}
			return contents.get(0);
		} else
			return "";
	}

	public void logChallenge(GeneAnnotation annot, List<GeneAnnotation> removed, String rationale) {
		LogEntry entry = new LogEntry(annot.getBioentityObject(), annot, LOG_ENTRY_TYPE.CHALLENGE, removed);
		entry.setDate(LogUtil.dateNow());
		entry.setRationale(rationale);
		done_log.add(entry);
		for (GeneAnnotation removed_annot : removed) {
			boolean cleared = false;
			for (int i = done_log.size() - 1; i >= 0 && !cleared; i--) {
				LogEntry assoc_entry = done_log.get(i);
				if (assoc_entry.getLoggedAssociation() == removed_annot) {
					done_log.remove(assoc_entry);
					cleared = true;
				}
			}
		}
	}

	public List<LogEntry> getDoneLog() {
		List<LogEntry> copy = new ArrayList<>();
		copy.addAll(done_log);
		return copy;
	}

}
