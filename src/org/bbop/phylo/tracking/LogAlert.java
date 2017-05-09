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

import org.bbop.phylo.model.Bioentity;
import org.bbop.phylo.model.GeneAnnotation;
import org.bbop.phylo.owl.OWLutil;

public class LogAlert {
	/**
	 *
	 */
	private static List<LogEntry> invalids;
	private static List<LogEntry> missing;
	private static List<LogEntry> obsoletes;

//	private static final org.apache.log4j.Logger logger = org.apache.log4j.Logger.getLogger(LogAlert.class);

	public static void clearLog() {
		if (invalids != null) {
			invalids.clear();
		} else {
			invalids = new ArrayList<>();
		}
		if (missing != null) {
			missing.clear();
		} else {
			missing = new ArrayList<>();
		}
		if (obsoletes != null) {
			obsoletes.clear();
		} else {
			obsoletes = new ArrayList<>();
		}
	}

	public static void logMissing(Bioentity node, GeneAnnotation assoc) {
		LogEntry entry = new LogEntry(node, assoc, LogEntry.LOG_ENTRY_TYPE.MISSING, null);
		missing.add(entry);
	}

	public static void logInvalid(Bioentity node, GeneAnnotation assoc, LogEntry.LOG_ENTRY_TYPE type) {
		LogEntry entry = new LogEntry(node, assoc, type, null);
		invalids.add(entry);
	}

	public static void logObsolete(Bioentity node, GeneAnnotation assoc) {
		LogEntry entry = new LogEntry(node, assoc, LogEntry.LOG_ENTRY_TYPE.OBSOLETE_TERM, null);
		obsoletes.add(entry);
	}

	public static int report(List<String> contents) {
		int count = 0;
		if ((invalids != null && !invalids.isEmpty()) 
				|| (missing != null && !missing.isEmpty()) 
				|| (obsoletes != null && !obsoletes.isEmpty())) {
			if (!invalids.isEmpty()) {
				count += invalids.size();
				contents.add("## " + invalids.size() +
				(invalids.size() == 1 ? " annotation is unsupported and has been removed." 
						: " annotations are unsupported and have been removed."));
				for (LogEntry entry : invalids) {
					GeneAnnotation annotation = entry.getLoggedAssociation();
					contents.add(annotation.getLastUpdateDate() + ": " +
							Logger.makeLabel(entry.getNode()) + " to " +
							OWLutil.inst().getTermLabel(annotation.getCls()) +
							" (" + annotation.getCls() + ") " + entry.getNotes());
				}
			}
			if (!missing.isEmpty()) {
				count += missing.size();
				contents.add("## " + missing.size() +
				(missing.size() == 1 ? " annotation is " : " annotations are ") + 
				"missing because the ancestral node is no longer found in this family");
				for (LogEntry entry : missing) {
					GeneAnnotation annotation = entry.getLoggedAssociation();
					if (annotation.isCut())
						contents.add(annotation.getLastUpdateDate() + ": " +
								entry.getNode().getDBID() +
								" was cut, but is now officially pruned from tree");
					else
						contents.add(annotation.getLastUpdateDate() + ": " +
								entry.getNode().getDBID() +
								" can not support previous annotation to " +
								OWLutil.inst().getTermLabel(annotation.getCls()) +
								" (" + annotation.getCls() + ") supported by " + annotation.getWithInfos());
				}
			}
			if (!obsoletes.isEmpty()) {
				count += obsoletes.size();
				contents.add("## " + obsoletes.size() +
						(obsoletes.size() == 1 ? " annotation was made to an obsolete term." :
							" annotations were made to obsolete terms."));
				for (LogEntry entry : obsoletes) {
					GeneAnnotation annotation = entry.getLoggedAssociation();
					contents.add(annotation.getLastUpdateDate() + ": " +
							entry.getNode().getDBID() +
							" removed annotation to obsolete term - " +
							OWLutil.inst().getTermLabel(annotation.getCls()) +
							" (" + annotation.getCls() + ") ");
				}
			}
		}
		contents.add("");
		return count;
	}
	
	public static List<String> report() {
		List<String> summary = new ArrayList<>();
		report(summary);
		return summary;
	}

	public static int getInvalidCount() {
		return (invalids == null) ? 0 : invalids.size();
	}

	public static int getMissingCount() {
		return (missing == null) ? 0 : missing.size();
	}

	public static int getObsoleteCount() {
		return (obsoletes == null) ? 0 : obsoletes.size();
	}
	
	public static int getAlertCount() {
		return getInvalidCount() + getMissingCount() + getObsoleteCount();
	}
}


