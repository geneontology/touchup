package org.bbop.phylo.io.panther;

import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;
import java.util.Vector;

import org.apache.log4j.Logger;
import org.bbop.phylo.model.Protein;
import org.bbop.phylo.util.Constant;

import owltools.gaf.Bioentity;
import owltools.gaf.species.TaxonFinder;

public class ParsingHack {

	private static final Logger log = Logger.getLogger(ParsingHack.class);

	private static String dbNameHack(String name) {
		/* The GO database is not using the suffix */
		String revision = name;
		if (name.equals("UniProtKB/Swiss-Prot") ||
				name.equals("Uniprot")) {
			revision = "UniProtKB";
		}
		if (name.equals("EnsemblGenome") || name.equalsIgnoreCase("ensembl")) {
			revision = "ENSEMBL";
		}
		else if (name.equals("ENTREZ")) {
			revision = "RefSeq";
		}
		else if (name.equals("ECOLI")) {
			revision = "EcoCyc";
		}
		else if (name.equals("GeneDB_Spombe")) {
			revision = "PomBase";
		}
		else if (name.equals("FlyBase")) {
			revision = "FB";
		}
		else if (name.equals("WormBase")) {
			revision = "WB";
		}
		return revision;
	}

	private static String dbIdHack(String db, String id) {
		String revision = id;
		if (useUniProtID(db)) {
			if (id.endsWith("gn")) {
				revision = id.substring(0, id.length() - "gn".length());
			}
		}
		else if (db.equals("TAIR")) {
			revision = id.toUpperCase();
		}
		return revision;
	}

	private static final String DELIMITER = "\t";
	private static final String DELIM_QUOTE = "'";
	private static final String DELIM_NEW_LINE = "\n";

	public static List<List<String>> parsePantherAttr(List<String> tableContents) {
		if (null == tableContents) {
			return null;
		}

		if (0 == tableContents.size()) {
			return null;
		}
		List<List<String>> rows = new ArrayList<List<String>>();
		List<String> columns;
		List<String> modifiedCols;
		int numCols = tokenize(tableContents.get(0), DELIMITER).size();
		int i = 0;
		while (i < tableContents.size()) {
			// Remove new line character from end
			String line = tableContents.get(i);
			if (line.endsWith(DELIM_NEW_LINE)) {
				tableContents.set(i, line.substring(0, line.length() - 1));
			}
			columns = tokenize(tableContents.get(i), DELIMITER);
			modifiedCols = removeQuotes(columns);
			if (numCols != modifiedCols.size()) {
				return null;
			}
			i++;
			rows.add(modifiedCols);
		}
		return rows;
	}

	public static Protein findThatNode(String row) {
		IDmap mapper = IDmap.inst();
		Protein gene = null;
		String paint_id = parseANid(row);

		if (paint_id != null)
			gene = mapper.getGeneByANId(paint_id);
		if (gene == null) {
			String [] db_source = getDBparts(row);
			String [] seq_source = getSeqParts(row);
			if (db_source == null || db_source.length == 0) {
				return null;
			}
			String db_name = dbNameHack(db_source[0]);			
			String db_id = dbIdHack(db_name, db_source[1]);
			String full_id = db_name + ':' + db_id;
			List<Protein> genes = mapper.getGenesBySeqId(seq_source[0], seq_source[1]);
			if (genes != null) {
				for (int i = 0; i < genes.size() && gene == null; i++) {
					Protein check = genes.get(i);
					if (check.getId().equals(full_id)) {
						gene = check;
					}
				}
			} 
			if (gene == null) {
				genes = mapper.getGeneByDbId(full_id);
		        if (genes != null && genes.size() == 1) {
		        	gene = genes.get(0);
		        } else {
					log.debug("S.o.o.L. for " + full_id);
		        	gene = null;
		        }
			}
		}
		return gene;
	}

	static void parseIDstr(Protein node, String idstr) {
		String paint_id = parseANid(idstr);
		if (paint_id != null)
			node.setPaintId(paint_id);
		else {
			String[] parts = getParts(idstr);
			if (parts != null && parts.length > 0) {
				String species = parts[0];
				/*
				 * Extremely ugly hack to deal with upstream typo
				 * Not red tile fish, but a proteobacteria
				 * 
				 */
				if (species.equals("BRAJA"))
					species = "BRADU";
				
				node.addSpeciesLabel(species);
				String taxon = TaxonFinder.getTaxonID(species);
				if (taxon != null) {
					node.setNcbiTaxonId(taxon);
				}
				String[] db_source = getDBparts(idstr);
				String[] seq_source = getSeqParts(idstr);
				/*
				 * Standard order from PANTHER Database is
				 * SPECI|GeneDbNname=gene_id|ProteinDbName=protein_id
				 * There may be multiple genes all with the same Protein ID
				 */
				if (db_source != null && db_source.length >= 2) {
					String db_name = dbNameHack(db_source[0]);
					String db_id = dbIdHack(db_name, db_source[1]);
					node.setDb(db_name);
					node.setId(node.getDb() + ':' + db_id);
					node.setSeqId(seq_source[0], seq_source[1]);
					IDmap.inst().indexByDBID(node);
					IDmap.inst().indexBySeqID(node);
					if (node.getSeqId() != null && node.getSeqId().length() > 0) {
						node.addSynonym(node.getSeqDb() +':' +  node.getSeqId());
					}
				} else {
					log.info("Couldn't get db from " + idstr);
				}
			}
		}
	}

	/*
	 * This is largely for searching GoLR, to use the 
	 * appropriate identifier from the submissions perspective
	 */
	public static boolean useUniProtID(String db_name) {
		if (db_name == null) {
			log.debug("Who did this?");
			return false;
		}
		boolean use_uniprot = (db_name.equals("GeneID") || 
				db_name.equals("Gene") ||
				db_name.equals("Xenbase") ||
				db_name.equals("ENSEMBL") || 
				db_name.equals("UniProtKB") ||
				db_name.equals("HGNC") ||
				db_name.equals("EcoGene"));
		if (!use_uniprot &&
				!db_name.equalsIgnoreCase("genedb") &&
				!db_name.equalsIgnoreCase("AspGD") &&
				!db_name.equalsIgnoreCase("CGD") &&
				!db_name.equalsIgnoreCase("dictyBase") &&
				!db_name.equalsIgnoreCase("FB") &&
				!db_name.equalsIgnoreCase("mgi") &&
				!db_name.equalsIgnoreCase("pombase") &&
				!db_name.equalsIgnoreCase("rgd") &&
				!db_name.equalsIgnoreCase("sgd") &&
				!db_name.equalsIgnoreCase("tair") &&
				!db_name.equalsIgnoreCase("wb") &&
				!db_name.equalsIgnoreCase("zfin")
				) {
			log.debug("Unknown Database name: " + db_name);
			use_uniprot = true;
		}
		return use_uniprot;
	}


	public static List<String> tokenize(String input, String delim) {
		List<String> v = new ArrayList<String>();
		StringTokenizer tk = new StringTokenizer(input, delim);
		while (tk.hasMoreTokens()) {
			v.add(tk.nextToken());
		}
		return v;
	}

	private static String parseANid(String name) {
		String [] parts = getParts(name);
		String paint_id = null;
		if (parts.length < 1) {
			paint_id = name;
		} else if (parts.length < 2) {
			paint_id = parts[0];
		}
		return paint_id;
	}

	private static String [] getSeqParts(String row) {
		String [] parts = getParts(row);
		String [] seq_source;
		if (parts.length >= 3) {
			if (parts[2].contains("=ENSTRUG") || parts[1].contains("=ENSTRUP")) {
				seq_source = parts[1].split(Constant.EQUAL);
			} else {
				seq_source = parts[2].split(Constant.EQUAL);
			}
			return seq_source;
		}
		else {
			return null;
		}
	}

	private static String [] getParts(String row) {
		if (row.charAt(row.length() - 1) == ';') {
			row = row.substring(0, row.length() - 1);
		}
		return row.split(Constant.PIPE);
	}

	private static String [] getDBparts(String row) {
		String [] parts = getParts(row);
		String [] db_source;
		/*
		 * Standard order from PANTHER Database is
		 * SPECI|DbGene=gene_id|ProteinSeq=protein_id
		 * There may be multiple genes all with the same Protein ID
		 */
		if (parts.length >= 3) {
			if (parts[2].contains("=ENSTRUG") || parts[1].contains("=ENSTRUP")) {
				db_source = parts[2].split(Constant.EQUAL);
				String [] seq_source = parts[1].split(Constant.EQUAL);
				log.info("Gene " + db_source[1] + " and protein " + seq_source[1] + " appear reversed in " + row);
			} else {
				db_source = parts[1].split(Constant.EQUAL);
				if (db_source.length == 3) {
					if (db_source[0].equals("MGI") || 
							db_source[0].equals("TAIR") || 
							db_source[0].equals("ECOLI")) {
						/*
						 * MOUSE|MGI=MGI=97788|UniProtKB=Q99LS3
						 * ARATH|TAIR=locus=2015008|NCBI=NP_176687
						 */
						db_source[1] = db_source[1] + ':' + db_source[2];
					}
					else if (db_source[0].equals("Gene")) {
						db_source[0] = db_source[1];
						db_source[1] = db_source[2];
					}
					else {
						log.info("Too many parts in " + parts[1]);
					}
				}
			}
			return db_source;
		} else {
			return null;
		}
	}

	private static Vector<String> removeQuotes(List<String> columns) {
		Vector<String> updated = new Vector<String>();
		for (int i = 0; i < columns.size(); i++) {
			String contents = columns.get(i);
			if (contents.startsWith(DELIM_QUOTE)) {
				contents = contents.substring(1);
				if (contents.endsWith(DELIM_QUOTE)) {
					contents = contents.substring(0, contents.length() - 1);
				}
			}
			updated.addElement(contents);
		}
		return updated;
	}


}
