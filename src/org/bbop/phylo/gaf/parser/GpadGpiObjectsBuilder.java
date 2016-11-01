package org.bbop.phylo.gaf.parser;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.zip.GZIPInputStream;

import org.apache.commons.io.IOUtils;
import org.apache.commons.lang3.StringUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.log4j.Logger;
import org.bbop.phylo.model.Bioentity;
import org.bbop.phylo.model.GeneAnnotation;

import gnu.trove.map.hash.THashMap;

public class GpadGpiObjectsBuilder {
	
	private static final Logger logger = Logger.getLogger(GpadGpiObjectsBuilder.class);

	// list of filters
	private List<LineFilter<GpadParser>> gpadFilters = null;
	private List<LineFilter<GpiParser>> gpiFilters = null;
	private List<IssueListener> issueListeners = null;
	private AspectProvider aspectProvider = null;
	private final SimpleEcoMapper ecoMapper;
	
	private boolean gpadIncludeUnknowBioentities = false;
	private boolean gpadIncludeUnmappedECO = true;
	
	public GpadGpiObjectsBuilder(SimpleEcoMapper ecoMapper) {
		this.ecoMapper = ecoMapper;
	}

	public synchronized void addGpadFilter(LineFilter<GpadParser> filter) {
		if (gpadFilters == null) {
			gpadFilters = new ArrayList<LineFilter<GpadParser>>();
		}
		gpadFilters.add(filter);
	}
	
	public synchronized void addGpiFilter(LineFilter<GpiParser> filter) {
		if (gpiFilters == null) {
			gpiFilters = new ArrayList<LineFilter<GpiParser>>();
		}
		gpiFilters.add(filter);
	}
	
	public synchronized void addIssueListener(IssueListener listener) {
		if (issueListeners == null) {
			issueListeners = new ArrayList<IssueListener>();
		}
		issueListeners.add(listener);
	}
	
	public boolean isGpadIncludeUnknowBioentities() {
		return gpadIncludeUnknowBioentities;
	}

	public void setGpadIncludeUnknowBioentities(boolean gpadIncludeUnknowBioentities) {
		this.gpadIncludeUnknowBioentities = gpadIncludeUnknowBioentities;
	}

	public boolean isGpadIncludeUnmappedECO() {
		return gpadIncludeUnmappedECO;
	}

	public void setGpadIncludeUnmappedECO(boolean gpadIncludeUnmappedECO) {
		this.gpadIncludeUnmappedECO = gpadIncludeUnmappedECO;
	}

	public Pair<BioentityDocument, GafDocument> loadGpadGpi(File gpad, File gpi) throws IOException {
		// 1. load GPI
		BioentityDocument entities = new BioentityDocument(gpi.getName());
		Map<String,Bioentity> mappings = loadGPI(getInputStream(gpi), entities);
		
		// create annotation document with bioentities
		GafDocument document = new GafDocument(gpad.getName(), gpad.getCanonicalPath(), mappings);
		
		// 2. load GPAD
		loadGPAD(getInputStream(gpad), document);
		
		return Pair.of(entities, document);
	}
	
	public void setAspectProvider(AspectProvider aspectProvider) {
		this.aspectProvider = aspectProvider;
	}
	
	public static interface AspectProvider {
		
		public String getAspect(String cls);
	}
	
	private InputStream getInputStream(File file) throws IOException {
		InputStream inputStream = new FileInputStream(file);
		String fileName = file.getName().toLowerCase();
		if (fileName.endsWith(".gz")) {
			inputStream = new GZIPInputStream(inputStream);
		}
		return inputStream;
	}
	
	private Map<String, Bioentity> loadGPI(InputStream inputStream, final BioentityDocument document) throws IOException {
		GpiParser parser = null;
		try {
			parser = new GpiParser();
			parser.addCommentListener(new CommentListener() {
				
				@Override
				public void readingComment(String comment, String line, int lineNumber) {
					document.addComment(comment);
				}
			});
			parser.createReader(inputStream);
			return loadBioentities(parser, document);
		}
		finally {
			IOUtils.closeQuietly(parser);
		}
	}
	
	private Map<String, Bioentity> loadBioentities(GpiParser parser, BioentityDocument document) throws IOException {
		Map<String, Bioentity> entities = new THashMap<String, Bioentity>();
		
		while(parser.next()) {
			// by default load everything
			boolean load = true;
			if (gpiFilters != null) {
				// check each filter
				for (LineFilter<GpiParser> filter : gpiFilters) {
					boolean accept = filter.accept(parser.getCurrentRow(), parser.getLineNumber(), parser);
					if (accept == false) {
						load = false;
						break;
					}
				}
			}
			if (load) {
				String namespace = parser.getNamespace();
				if (namespace != null) {
					Bioentity bioentity = parseBioentity(parser);
					entities.put(bioentity.getId(), bioentity);
					document.addBioentity(bioentity);
				}
			}
		}
		return entities;
	}
	
	private void loadGPAD(InputStream inputStream, GafDocument document) throws IOException {
		GpadParser parser = null;
		try {
			parser = new GpadParser();
			parser.createReader(inputStream);
			loadGeneAnnotations(parser, document);
		}
		finally {
			IOUtils.closeQuietly(parser);
		}
	}
	
	private void loadGeneAnnotations(GpadParser parser, final GafDocument document) throws IOException {
		parser.addCommentListener(new CommentListener() {
			
			@Override
			public void readingComment(String comment, String line, int lineNumber) {
				document.addComment(comment);
			}
		});
		while(parser.next()) {
			// by default load everything
			boolean load = true;
			if (gpiFilters != null) {
				// check each filter
				for (LineFilter<GpadParser> filter : gpadFilters) {
					boolean accept = filter.accept(parser.getCurrentRow(), parser.getLineNumber(), parser);
					if (accept == false) {
						load = false;
						break;
					}
				}
			}
			if (load) {
				GeneAnnotation annotation = parseAnnotation(parser, document, aspectProvider, ecoMapper);
				if (annotation != null) {
					document.addGeneAnnotation(annotation);
				}
			}
		}
	}

	private Bioentity parseBioentity(GpiParser parser) {
		String db = parser.getNamespace();
		String bioentityId = db + ":" + parser.getDB_Object_ID();
		Bioentity entity = new Bioentity(bioentityId,
				parser.getDB_Object_Symbol(), parser.getDB_Object_Name(),
				parser.getDB_Object_Type(),
				BuilderTools.handleTaxonPrefix(parser.getTaxon()), db);

		BuilderTools.addSynonyms(parser.getDB_Object_Synonym(), entity);
		entity.setGeneId(parser.getParent_Object_ID());
		BuilderTools.addXrefs(parser.getDB_Xref(), entity);
		BuilderTools.addProperties(parser.getGene_Product_Properties(), entity);
		return entity;
	}
	
	protected void reportUnknowBioentityId(String fullId, boolean fatal) {
		final String msg = "No Bioentity found for id.";
		if (issueListeners != null) {
			for (IssueListener listener : issueListeners) {
				listener.reportIssue(fullId, msg, fatal);
			}
		}
		if (fatal) {
			logger.error("Skipping annotation using unknown Bioentity: "+fullId);
		}
		else {
			logger.warn("No Bioentity found for id: "+fullId);
		}
	}
	
	protected void reportEvidenceIssue(String eco, String msg, boolean fatal) {
		if (issueListeners != null) {
			for (IssueListener listener : issueListeners) {
				listener.reportIssue(eco, msg, fatal);
			}
		}
		if (fatal) {
			logger.error(msg+" "+eco);
		}
		else {
			logger.warn(msg+" "+eco);
		}
	}
	
	private GeneAnnotation parseAnnotation(GpadParser parser, GafDocument document, AspectProvider aspectProvider, SimpleEcoMapper mapper) {
		GeneAnnotation ga = new GeneAnnotation();
		String cls = parser.getGO_ID();
		
		// col 1-2
		String bioentityId = parser.getDB() + ":" + parser.getDB_Object_ID();
		Bioentity entity = document.getBioentity(bioentityId);
		if (entity == null) {
			boolean fatal = gpadIncludeUnknowBioentities == false;
			reportUnknowBioentityId(bioentityId, fatal);
			if (fatal) {
				return null;
			}
			ga.setBioentity(bioentityId);
		}
		else {
			// check for iso form
			final String parentObjectId = StringUtils.trimToNull(entity.getGeneId());
			if (parentObjectId != null) {
				ga.setBioentity(parentObjectId);
				ga.setGeneProductForm(bioentityId);
				final Bioentity parentBioentity = document.getBioentity(parentObjectId);
				if (parentBioentity != null) {
					ga.setBioentityObject(parentBioentity);
				}
				else {
					boolean fatal = gpadIncludeUnknowBioentities == false;
					reportUnknowBioentityId(parentObjectId, fatal);
					if (fatal) {
						return null;
					}
				}
			}
			else {
				ga.setBioentity(entity.getId());
				ga.setBioentityObject(entity);
			}
		}

		// col 3
		BuilderTools.parseQualifiers(ga, parser.getQualifier(), parser);
		
		String relation = null;
		String aspect = "";
		if (aspectProvider != null) {
			aspect = aspectProvider.getAspect(cls);
			if (aspect != null && relation == null) {
				if (aspect.equals("F")) {
					relation = "enables";
				} else if (aspect.equals("P")) {
					relation = "involved_in";
				} else if (aspect.equals("C")) {
					relation = "part_of";
				}
			}
		}
		
		if (ga.isContributesTo())
			relation = "contributes_to";
		if (ga.isColocatesWith())
			relation = "colocalizes_with";
		
		ga.setRelation(relation);
		ga.setAspect(aspect);
		
		// col 4
		ga.setCls(cls);
		
		// col 5
		BuilderTools.addXrefs(parser.getDB_Reference(), ga);
		
		// col 6
		boolean added = addEvidenceCode(parser.getEvidence_Code(), ga, mapper);
		if (!added) {
			return null;
		}
		
		// col 7 with
		ga.setWithInfos(BuilderTools.parseWithInfo(parser.getWith()));
		
		// col8
		ga.setActsOnTaxonId(BuilderTools.parseTaxonRelationshipPair(parser.getInteracting_Taxon_ID()));
		
		// col 9
		ga.setLastUpdateDate(parser.getDate());
		
		// col 10
		ga.setAssignedBy(parser.getAssigned_by());
		
		// col 11
		String extensionExpression = parser.getAnnotation_Extension();
		List<List<ExtensionExpression>> extensionExpressionList = BuilderTools.parseExtensionExpression(extensionExpression);
		ga.setExtensionExpressions(extensionExpressionList);
		
		// col 12
		BuilderTools.addProperties(parser.getAnnotation_Properties(), ga);
		
		return ga;
	}
	
	private boolean addEvidenceCode(String eco, GeneAnnotation ga, SimpleEcoMapper mapper) {
		Pair<String,String> pair = mapper.getGoCode(eco);
		boolean added = false;
		if (pair != null) {
			String goCode = pair.getLeft();
			if (goCode != null) {
				ga.setEvidence(goCode, eco);
				added = true;
			}
		}
		if (added == false) {
			boolean fatal = gpadIncludeUnmappedECO == false;
			reportEvidenceIssue(eco, "No corresponding GO evidence code found", fatal);
			if (fatal) {
				return false;
			}
			// fallback always add the ECO class at least
			ga.setEvidence(null, eco);
		}
		return true;
	}
}
