package org.bbop.phylo.owl;
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


import java.io.Closeable;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;
import org.bbop.phylo.annotate.AnnotationUtil;
import org.bbop.phylo.gaf.parser.DefaultAspectProvider;
import org.bbop.phylo.gaf.parser.GpadGpiObjectsBuilder.AspectProvider;
import org.bbop.phylo.model.Bioentity;
import org.bbop.phylo.model.GeneAnnotation;
import org.bbop.phylo.util.TimerUtil;
import org.geneontology.reasoner.ExpressionMaterializingReasoner;
import org.obolibrary.oboformat.parser.OBOFormatParserException;
import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.util.OWLClassExpressionVisitorAdapter;

import com.google.common.collect.Sets;
import com.google.common.collect.Sets.SetView;

public class OWLutil {

	protected static Logger log = Logger.getLogger(OWLutil.class);

	private final OWLGraphWrapper go_graph;
	private final AncestorTool ancestor_tool;
	private final AspectProvider aspect_provider;
	private final Map<String, OWLClass> OWLclasses;
	private final Map<String, String> term_labels;
	private final Set<OWLObjectProperty> isaPartOf;
	private final Set<OWLObjectProperty> isaPartOfRegulates;

	private static final int LESS_THAN = -1;
	private static final int GREATER_THAN = 1;
	private static final int EQUAL_TO = 0;

	private static class AncestorTool implements Closeable {

		private final Set<OWLObjectProperty> materializedProperties;
		private final ExpressionMaterializingReasoner reasoner;

		public AncestorTool(OWLOntology source, Set<OWLObjectProperty> materializedProperties, int cacheSize) {
			super();
			this.materializedProperties = materializedProperties;
			reasoner = new ExpressionMaterializingReasoner(source, new ElkReasonerFactory());
			reasoner.materializeExpressions(materializedProperties);
		}

		public OWLReasoner getReasoner() {
			return reasoner;
		}

		@Override
		public void close() throws IOException {
			reasoner.dispose();
		}

		public Set<OWLClass> getAncestorClosure(OWLClass c, final Set<OWLObjectProperty> relations){
			return createAncestorClosure(c, relations);
		}

		public Set<OWLClass> createAncestorClosure(OWLClass obj, Set<OWLObjectProperty> relations){

			final Set<OWLClass> ancestors = new HashSet<>(); //

			// reflexive
			ancestors.add(obj);

			findAncestors(obj, relations, ancestors);
			return ancestors;
		}

		private void findAncestors(OWLClass c, final Set<OWLObjectProperty> props, final Set<OWLClass> ancestors) {
			if (materializedProperties.containsAll(props) == false) {
				SetView<OWLObjectProperty> missing = Sets.difference(props, materializedProperties);
				throw new RuntimeException("Unable to use the following properties as they are not in the pre-materialized set: "+missing);
			}
			Set<OWLClassExpression> classExpressions = reasoner.getSuperClassExpressions(c, false);
			for (OWLClassExpression ce : classExpressions) {
				OWLClassExpressionVisitorAdapter visitor = new OWLClassExpressionVisitorAdapter() {

					@Override
					public void visit(OWLClass cls) {
						if (cls.isBuiltIn() == false) {
							ancestors.add(cls);
						}
					}

					@Override
					public void visit(OWLObjectSomeValuesFrom svf) {
						OWLClassExpression filler = svf.getFiller();
						OWLObjectPropertyExpression p = svf.getProperty();
						if (props.contains(p)) {
							if (!filler.isAnonymous()) {
								OWLClass cls = filler.asOWLClass();
								ancestors.add(cls);
							}
						}
					}

				};
				ce.accept(visitor);
			}
		}
	}

	private OWLutil () {
		try {
			TimerUtil timer = new TimerUtil();
			log.info("Begin loading GO");
			ParserWrapper pw = new ParserWrapper();
			String iriString = "http://purl.obolibrary.org/obo/go.obo";
			go_graph = new OWLGraphWrapper(pw.parse(iriString));
			
			log.info("GO retrieved " + timer.reportElapsedTime());

			OWLclasses = new HashMap<>();
			term_labels = new HashMap<>();
			OWLObjectProperty part_of = go_graph.getOWLObjectPropertyByIdentifier("BFO:0000050"); // part_of
			OWLObjectProperty regulates = go_graph.getOWLObjectPropertyByIdentifier("RO:0002211"); // regulates
			OWLObjectProperty pos_regulates = go_graph.getOWLObjectPropertyByIdentifier("RO:0002213"); // positively regulates
			OWLObjectProperty neg_regulates = go_graph.getOWLObjectPropertyByIdentifier("RO:0002212"); // negatively regulates
			isaPartOf = Collections.<OWLObjectProperty>singleton(part_of);
			isaPartOfRegulates = new HashSet<>();
			isaPartOfRegulates.add(part_of);
			isaPartOfRegulates.add(regulates);
			isaPartOfRegulates.add(neg_regulates);
			isaPartOfRegulates.add(pos_regulates);

			ancestor_tool = new AncestorTool(go_graph.getSourceOntology(), isaPartOfRegulates, 10000);

			Map<String, String> mappings = new HashMap<String, String>();
			mappings.put("GO:0008150", "P");
			mappings.put("GO:0003674", "F");
			mappings.put("GO:0005575", "C");

			aspect_provider = DefaultAspectProvider.createAspectProvider(go_graph, mappings, ancestor_tool.getReasoner());
			
			log.info("GO relations loaded " + timer.reportElapsedTime());

		} catch (OWLOntologyCreationException e) {
			throw new RuntimeException(e);
		} catch (OBOFormatParserException e) {
			throw new RuntimeException(e);
		} catch (IOException e) {
			throw new RuntimeException(e);
		} catch (Exception e) {
			throw e;
		}
	}

	private static volatile OWLutil INSTANCE = null;

	public static OWLutil inst() {
		if (INSTANCE == null) {
			synchronized (OWLutil.class) {
				if (INSTANCE == null) {
					INSTANCE = new OWLutil();
				}
			}
		}
		return INSTANCE;
	}

	/*
		to avoid overuse of memory reset the term hash
		after a new family is loaded
	 */
	public void clearTerms() {
		if (OWLclasses != null) {
			OWLclasses.clear();
			term_labels.clear();
			System.gc();
		}
	}

	public  boolean isObsolete(String go_id) {
		OWLClass term = getTerm(go_id);
		return term == null || (term != null && go_graph.isObsolete(term));
	}

	public  List<String> replacedBy(String go_id) {
		OWLClass term = getTerm(go_id);
		List<String> go_ids;
		if (term != null) {
			go_ids = go_graph.getReplacedBy(term);
			if (go_ids != null) {
				if (go_ids.size() > 1) {
					log.info("More than one replacement term for " + term);
				}
			} else {
				log.info("No replacement for obsolete term " + term);
			}
		} else {
			go_ids = new ArrayList<>();
			/* try looking it up as an alt-id */
			term = go_graph.getOWLClassByIdentifier(go_id, true);
			if (term != null) {
				String term_id = go_graph.getIdentifier(term);
				OWLclasses.put(term_id, term);
				setTermLabel(term_id);
				go_ids.add(term_id);
			}

		}
		return go_ids;
	}

	public  boolean isExcluded(String go_id) {
		OWLClass term = getTerm(go_id);
		return isExcluded(term);
	}

	private  boolean isExcluded(OWLClass term) {
		List<String> subsets = go_graph.getSubsets(term);
		boolean isExcluded = false;
		for(String subset : subsets) {
			if ("gocheck_do_not_manually_annotate".equals(subset) || "gocheck_do_not_annotate".equals(subset)) {
				isExcluded = true;
				break;
			}
		}
		return isExcluded;
	}

	public  String getTermLabel(String go_id) {
		String label = term_labels.get(go_id);
		if (label == null) {
			label = setTermLabel(go_id);
		}
		return label;
	}

	private  String setTermLabel(String go_id) {
		String label;
		OWLClass term = getTerm(go_id);
		if (term != null) {
			label = go_graph.getLabelOrDisplayId(term);
		} else {
			label = go_id + " no label";
		}
		term_labels.put(go_id, label);
		return label;
	}

	public  String getAspect(String term_id) {
		String aspect;
		aspect = aspect_provider.getAspect(term_id);
		return aspect;
	}

	public  boolean moreSpecific(String check_term, String against_term) {
		return moreSpecific(check_term, against_term, isaPartOf);
	}

	public  boolean moreSpecific(String check_term, String against_term, boolean regulates) {
		return moreSpecific(check_term, against_term, isaPartOfRegulates);
	}

	private  boolean moreSpecific(String check_term, String against_term, Set<OWLObjectProperty> relations) {
		OWLClass check = getTerm(check_term);
		OWLClass against = getTerm(against_term);
		return moreSpecific(check, against, relations);
	}

	private  boolean moreSpecific(OWLClass o1, OWLClass o2, Set<OWLObjectProperty> relations) {
		Set<OWLClass> broader_terms = ancestor_tool.getAncestorClosure(o1, relations);
		if (broader_terms == null || o2 == null) {
			return false; // ?? not sure what to do in this case
		} else {
			return broader_terms.contains(o2);
		}
	}

	public  List<String> getAncestors(String term) {
		OWLClass check = getTerm(term);
		Set<OWLClass> broader_terms = ancestor_tool.getAncestorClosure(check, isaPartOfRegulates);
		List<String> ancestors = new ArrayList<>();
		List<OWLClass> sortedClasses = new ArrayList<OWLClass>(broader_terms);
		Collections.sort(sortedClasses, new Comparator<OWLClass>() {

			@Override
			public int compare(OWLClass o1, OWLClass o2) {
				/*
				 * Within a single aspect we want the more specific terms first
				 */
				if (moreSpecific(o1, o2, isaPartOf)) {
					return LESS_THAN;
				} else if (moreSpecific(o2, o1, isaPartOf)) {
					return GREATER_THAN;
				} else {
					return EQUAL_TO;
				}
			}
		});

		String aspect = getAspect(term);
		if (aspect != null) {
			for (OWLClass owlClass : sortedClasses) {
				String cls = go_graph.getIdentifier(owlClass);
				String cls_aspect = getAspect(cls);
				if (aspect.equals(cls_aspect) && !isExcluded(owlClass)) {
					ancestors.add(cls);
				}
			}
		} else {
			// add it anyway, not log it
			ancestors.add(term);
			log.info(term + " does not have an aspect defined");
		}
		return ancestors;
	}

	public  boolean descendantsAllBroader(Bioentity node, String go_id, boolean all_broader) {
		List<GeneAnnotation> associations = AnnotationUtil.getExperimentalAssociations(node);
		OWLClass annot_term = getTerm(go_id);
		Set<OWLClass> broader_terms = ancestor_tool.getAncestorClosure(annot_term, Collections.<OWLObjectProperty>emptySet());
		if (associations != null) {
			for (GeneAnnotation annotation : associations) {
				// since we've decided to always do positive annotations with NOTs being added afterwards, should make sure that
				// the association is positive
				if (!annotation.isNegated()) {
					String annot_id = annotation.getCls();
					if ((annotation.isMRC() || node.isLeaf())) {
						/*
						 * First argument is the parent term, second term is the descendant
						 * returns true if 2nd argument is a descendant of the 1st argument 
						 */
						all_broader &= (!go_id.equals(annot_id)) && (broader_terms.contains(getTerm(annot_id)));
					}
				}
			}
		}
		List<Bioentity> children = node.getChildren();
		if (all_broader && children != null) {
			for (Bioentity child : children) {
				all_broader &= descendantsAllBroader(child, go_id, all_broader);
			}
		}
		return all_broader;
	}

	public OWLClass getTerm(String go_id) {
		OWLClass term = OWLclasses.get(go_id);
		if (term == null) {
			term = go_graph.getOWLClassByIdentifier(go_id);
			OWLclasses.put(go_id, term);
		}
		return term;
	}
}
