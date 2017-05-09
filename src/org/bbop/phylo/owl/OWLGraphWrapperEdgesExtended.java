package org.bbop.phylo.owl;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.Vector;

import org.apache.log4j.Logger;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.OWLAnnotationProperty;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLNamedObject;
import org.semanticweb.owlapi.model.OWLObject;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLPropertyExpression;
import org.semanticweb.owlapi.model.OWLSubAnnotationPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.UnknownOWLOntologyException;

import org.bbop.phylo.owl.OWLGraphEdge.OWLGraphEdgeSet;
import org.bbop.phylo.owl.OWLQuantifiedProperty.Quantifier;

/**
 * This class groups methods that could be modified, or added 
 * to <code>OWLGraphWrapper</code> and parent classes.
 * 
 * @author Frederic Bastian
 * @version October 2014
 * @since November 2013
 *
 */
public class OWLGraphWrapperEdgesExtended extends OWLGraphWrapperEdges {
    private static final Logger LOG = Logger.getLogger(OWLGraphWrapperEdgesExtended.class);
	/**
	 * A cache for super property relations. Each <code>OWLObjectPropertyExpression</code> 
	 * is associated in the <code>Map</code> to a <code>LinkedHashSet</code> of 
	 * <code>OWLObjectPropertyExpression</code>s, that contains its super properties, 
	 * ordered from the more specific to the more general 
	 * (for instance, "in_deep_part_of", then "part_of", then "overlaps").
	 * @see #getSuperPropertyReflexiveClosureOf(OWLObjectPropertyExpression)
	 */
	private Map<OWLObjectPropertyExpression, LinkedHashSet<OWLObjectPropertyExpression>>
	    superPropertyCache;
	
	/**
	 * A cache for sub-property relations. Each <code>OWLObjectPropertyExpression</code> 
	 * is associated in the <code>Map</code> to a <code>LinkedHashSet</code> of 
	 * <code>OWLObjectPropertyExpression</code>s, that contains its sub-properties, 
	 * ordered from the more general to the more specific 
	 * (for instance, "overlaps", then "part_of", then "in_deep_part_of").
	 * @see #getSubPropertyClosureOf(OWLObjectPropertyExpression)
	 */
	private Map<OWLObjectPropertyExpression, LinkedHashSet<OWLObjectPropertyExpression>>
	    subPropertyCache;

    /**
     * A cache for relations to sub annotation properties. Each <code>OWLAnnotationProperty</code> 
     * is associated in the <code>Map</code> to a <code>LinkedHashSet</code> of 
     * <code>OWLAnnotationProperty</code>s, that contains its sub-properties, 
     * ordered from the more general to the more specific 
     * @see #getSubAnnotationPropertyClosureOf(OWLAnnotationProperty)
     */
    private Map<OWLAnnotationProperty, LinkedHashSet<OWLAnnotationProperty>>
        subAnnotationPropertyCache;
    
    /**
     * A {@code Map} storing OBO GCI relations, where keys are {@code OWLClass}es 
     * that are sources of a GCI relation, the associated value being 
     * a {@code Set} of {@code OWLGraphEdge}s representing the GCI relations, 
     * expanded to reach a named target. 
     * {@link OWLGraphEdge#isGCI()} will always return {@code true} for 
     * the {@code OWLGraphEdge}s stored in this {@code Map}.
     * @see #lazyLoadGCIRelCache()
     * @see #gciRelationByTarget
     */
    private Map<OWLClass, Set<OWLGraphEdge>> gciRelationBySource;
    /**
     * A {@code Map} storing OBO GCI relations, where keys are {@code OWLClass}es 
     * that are named targets of a GCI relation, the associated value being 
     * a {@code Set} of {@code OWLGraphEdge}s representing the GCI relations. 
     * {@link OWLGraphEdge#isGCI()} will always return {@code true} for 
     * the {@code OWLGraphEdge}s stored in this {@code Map}.
     * @see #lazyLoadGCIRelCache()
     * @see #gciRelationBySource
     */
    private Map<OWLClass, Set<OWLGraphEdge>> gciRelationByTarget;
    /**
     * A {@code Map} caching graph closures retrieved from 
     * {@link #getOutgoingEdgesClosureWithGCI(OWLObject)}. Keys are the source 
     * of the associated {@code OWLGraphEdges}.
     */
    private Map<OWLObject, Set<OWLGraphEdge>>  outgoingEdgesClosureWithGCIBySource;

	/**
	 * Default constructor. 
	 * @param ontology 		The <code>OWLOntology</code> that this object wraps.
	 */
	public OWLGraphWrapperEdgesExtended(OWLOntology ontology) {
		super(ontology);
    	this.subPropertyCache = new HashMap<OWLObjectPropertyExpression, 
    			LinkedHashSet<OWLObjectPropertyExpression>>();
        this.subAnnotationPropertyCache = new HashMap<OWLAnnotationProperty, 
                LinkedHashSet<OWLAnnotationProperty>>();
    	this.superPropertyCache = new HashMap<OWLObjectPropertyExpression, 
    			LinkedHashSet<OWLObjectPropertyExpression>>();
    	this.gciRelationBySource = null;
        this.gciRelationByTarget = null;
        this.outgoingEdgesClosureWithGCIBySource = null;
	}
	
	protected OWLGraphWrapperEdgesExtended(String iri)
			throws UnknownOWLOntologyException, OWLOntologyCreationException {
		super(iri);
    	this.subPropertyCache = new HashMap<OWLObjectPropertyExpression, 
    			LinkedHashSet<OWLObjectPropertyExpression>>();
    	this.superPropertyCache = new HashMap<OWLObjectPropertyExpression, 
    			LinkedHashSet<OWLObjectPropertyExpression>>();
        this.gciRelationBySource = null;
        this.gciRelationByTarget = null;
        this.outgoingEdgesClosureWithGCIBySource = null;
	}
   	
    /**
     * Determine if <code>testObject</code> belongs to at least one of the subsets 
     * in <code>subsets</code>. 
     * 
     * @param testObject	An <code>OWLObject</code> for which we want to know if it belongs 
     * 						to a subset in <code>subsets</code>.
     * @param subsets		A <code>Collection</code> of <code>String</code>s that are 
     * 						the names of the subsets for which we want to check belonging 
     * 						of <code>testObject</code>.
     * @return				<code>true</code> if <code>testObject</code> belongs to a subset 
     * 						in <code>subsets</code>, <code>false</code> otherwise.
     */
    public boolean isOWLObjectInSubsets(OWLObject testObject, Collection<String> subsets) {
    	return !Collections.disjoint(subsets, this.getSubsets(testObject));
    }
    

    /**
     * Returns the direct child properties of <code>prop</code> in all ontologies.
     * @param prop      The <code>OWLAnnotationProperty</code> for which 
     *                  we want the direct sub-properties.
     * @return          A <code>Set</code> of <code>OWLAnnotationProperty</code>s 
     *                  that are the direct sub-properties of <code>prop</code>.
     * 
     * @see #getSubPropertyClosureOf(OWLObjectPropertyExpression)
     * @see #getSubPropertyReflexiveClosureOf(OWLObjectPropertyExpression)
     */
    public Set<OWLAnnotationProperty> getSubAnnotationPropertiesOf(
            OWLAnnotationProperty prop) {
        Set<OWLAnnotationProperty> subProps = new HashSet<OWLAnnotationProperty>();
        for (OWLOntology ont : this.getAllOntologies()) {
            //we need to iterate each annotation property, to get 
            //its getSubAnnotationPropertyOfAxioms and see if prop is its parent 
            //(there is no method "getSuperAnnotationPropertyOfAxioms").
            for (OWLAnnotationProperty subProp : ont.getAnnotationPropertiesInSignature()) {
                for (OWLSubAnnotationPropertyOfAxiom ax: 
                        ont.getSubAnnotationPropertyOfAxioms(subProp)) {
                    if (ax.getSuperProperty().equals(prop)) {
                        subProps.add(subProp);
                    }
                }
            }
        }
        return subProps;
    }
    /**
     * Returns all child properties of <code>prop</code> in all ontologies,  
     * ordered from the more general (closer from <code>prop</code>) to the more precise. 
     * 
     * @param prop  the <code>OWLAnnotationProperty</code> for which we want 
     *              the ordered sub-properties. 
     * @return      A <code>LinkedHashSet</code> of <code>OWLAnnotationProperty</code>s 
     *              ordered from the more general to the more precise.
     * 
     * @see #getSubAnnotationPropertiesOf(OWLAnnotationProperty)
     * @see #getSubAnnotationPropertyReflexiveClosureOf(OWLAnnotationProperty)
     */
    //TODO: DRY, it is almost the same code as getSubPropertyClosureOf
    public LinkedHashSet<OWLAnnotationProperty> getSubAnnotationPropertyClosureOf(
            OWLAnnotationProperty prop) {
        //try to get the sub-properties from the cache
        LinkedHashSet<OWLAnnotationProperty> subProps = 
                this.subAnnotationPropertyCache.get(prop);
        if (subProps != null) {
            return subProps;
        }
        subProps = new LinkedHashSet<OWLAnnotationProperty>();
        Stack<OWLAnnotationProperty> stack = new Stack<OWLAnnotationProperty>();
        stack.add(prop);
        while (!stack.isEmpty()) {
            OWLAnnotationProperty nextProp = stack.pop();
            Set<OWLAnnotationProperty> directSubs = this.getSubAnnotationPropertiesOf(nextProp);
            directSubs.removeAll(subProps);
            stack.addAll(directSubs);
            subProps.addAll(directSubs);
        }
        //put the sub-properties in cache
        this.subAnnotationPropertyCache.put(prop, subProps);
        
        return subProps;
    }
    /**
     * Returns all sub-properties of <code>prop</code> in all ontologies, 
     * and <code>prop</code> itself as the first element (reflexive). 
     * The returned sub-properties are ordered from the more general (the closest 
     * from <code>prop</code>) to the more precise.
     * 
     * @param prop  the <code>OWLAnnotationProperty</code> for which we want 
     *              the ordered sub-properties. 
     * @return      A <code>LinkedHashSet</code> of <code>OWLAnnotationProperty</code>s 
     *              ordered from the more general to the more precise, with <code>prop</code> 
     *              as the first element. 
     * 
     * @see #getSubAnnotationPropertiesOf(OWLAnnotationProperty)
     * @see #getSubAnnotationPropertyClosureOf(OWLAnnotationProperty)
     */
    public LinkedHashSet<OWLAnnotationProperty> getSubAnnotationPropertyReflexiveClosureOf(
            OWLAnnotationProperty prop) {
        
        LinkedHashSet<OWLAnnotationProperty> subProps = 
                new LinkedHashSet<OWLAnnotationProperty>();
        
        subProps.add(prop);
        subProps.addAll(this.getSubAnnotationPropertyClosureOf(prop));
        
        return subProps;
    }
    
    /**
	 * Returns the direct child properties of <code>prop</code> in all ontologies.
	 * @param prop 		The <code>OWLObjectPropertyExpression</code> for which 
	 * 					we want the direct sub-properties.
	 * @return 			A <code>Set</code> of <code>OWLObjectPropertyExpression</code>s 
	 * 					that are the direct sub-properties of <code>prop</code>.
     * 
     * @see #getSubPropertyClosureOf(OWLObjectPropertyExpression)
     * @see #getSubPropertyReflexiveClosureOf(OWLObjectPropertyExpression)
	 */
	public Set<OWLObjectPropertyExpression> getSubPropertiesOf(
			OWLObjectPropertyExpression prop) {
		Set<OWLObjectPropertyExpression> subProps = new HashSet<OWLObjectPropertyExpression>();
		for (OWLOntology ont : this.getAllOntologies()) {
			for (OWLSubObjectPropertyOfAxiom axiom : 
				    ont.getObjectSubPropertyAxiomsForSuperProperty(prop)) {
				subProps.add(axiom.getSubProperty());
			}
		}
		return subProps;
	}
	/**
     * Returns all child properties of <code>prop</code> in all ontologies,  
     * ordered from the more general (closer from <code>prop</code>) to the more precise 
     * (e.g., for the "overlaps" property, return "part_of" then "in_deep_part_of"). 
     * 
     * @param prop 	the <code>OWLObjectPropertyExpression</code> for which we want 
     * 				the ordered sub-properties. 
     * @return		A <code>LinkedHashSet</code> of <code>OWLObjectPropertyExpression</code>s 
     * 				ordered from the more general to the more precise.
     * 
     * @see #getSubPropertiesOf(OWLObjectPropertyExpression)
     * @see #getSubPropertyReflexiveClosureOf(OWLObjectPropertyExpression)
     */
	public LinkedHashSet<OWLObjectPropertyExpression> getSubPropertyClosureOf(
			OWLObjectPropertyExpression prop) {
		//try to get the sub-properties from the cache
		LinkedHashSet<OWLObjectPropertyExpression> subProps = 
				this.subPropertyCache.get(prop);
		if (subProps != null) {
			return subProps;
		}
    	subProps = new LinkedHashSet<OWLObjectPropertyExpression>();
		Stack<OWLObjectPropertyExpression> stack = new Stack<OWLObjectPropertyExpression>();
		stack.add(prop);
		while (!stack.isEmpty()) {
			OWLObjectPropertyExpression nextProp = stack.pop();
			Collection<OWLObjectPropertyExpression> directSubs = this.getSubPropertiesOf(nextProp);
			directSubs.removeAll(subProps);
			if (directSubs.size() > 1) {
				// sort for deterministic behavior
				List<OWLObjectPropertyExpression> sorter = new ArrayList<OWLObjectPropertyExpression>(directSubs);
				Collections.sort(sorter);
				directSubs = sorter;
			}
			stack.addAll(directSubs);
			subProps.addAll(directSubs);
		}
		//put the sub-properties in cache
		this.subPropertyCache.put(prop, subProps);
		
		return subProps;
	}
	/**
     * Returns all sub-properties of <code>prop</code> in all ontologies, 
     * and <code>prop</code> itself as the first element (reflexive). 
     * The returned sub-properties are ordered from the more general (the closest 
     * from <code>prop</code>) to the more precise.
     * For instance, if <code>prop</code> is "overlaps", the returned properties will be  
     * "overlaps", then "part_of", then "in_deep_part_of", .... 
     * 
     * @param prop 	the <code>OWLObjectPropertyExpression</code> for which we want 
     * 				the ordered sub-properties. 
     * @return		A <code>LinkedHashSet</code> of <code>OWLObjectPropertyExpression</code>s 
     * 				ordered from the more general to the more precise, with <code>prop</code> 
     * 				as the first element. 
     * 
     * @see #getSubPropertiesOf(OWLObjectPropertyExpression)
     * @see #getSubPropertyClosureOf(OWLObjectPropertyExpression)
     */
	public LinkedHashSet<OWLObjectPropertyExpression> getSubPropertyReflexiveClosureOf(
			OWLObjectPropertyExpression prop) {
		
		LinkedHashSet<OWLObjectPropertyExpression> subProps = 
				new LinkedHashSet<OWLObjectPropertyExpression>();
		
		subProps.add(prop);
		subProps.addAll(this.getSubPropertyClosureOf(prop));
		
		return subProps;
	}
	
    /**
     * Returns all parent properties of <code>prop</code> in all ontologies, 
     * and <code>prop</code> itself as the first element (reflexive). 
     * Unlike the method <code>owltools.graph.OWLGraphWrapperEdges.getSuperPropertyReflexiveClosureOf</code>, 
     * the returned super properties here are ordered from the more precise to the more general 
     * (e.g., "in_deep_part_of", then "part_of", then "overlaps"). 
     * 
     * @param prop 	the <code>OWLObjectPropertyExpression</code> for which we want 
     * 				the ordered super properties. 
     * @return		A <code>LinkedHashSet</code> of <code>OWLObjectPropertyExpression</code>s 
     * 				ordered from the more precise to the more general, with <code>prop</code> 
     * 				as the first element. 
     */
	//TODO: Remove if OWLGraphWrapper changes its implementation
    public LinkedHashSet<OWLObjectPropertyExpression> getSuperPropertyReflexiveClosureOf(
    		OWLObjectPropertyExpression prop) {
    	
    	//try to get the super properties from the cache
    	LinkedHashSet<OWLObjectPropertyExpression> superProps = 
    			this.superPropertyCache.get(prop);
    	if (superProps == null) {

    		superProps = new LinkedHashSet<OWLObjectPropertyExpression>();
    		Stack<OWLObjectPropertyExpression> stack = 
    				new Stack<OWLObjectPropertyExpression>();
    		stack.add(prop);
    		while (!stack.isEmpty()) {
    			OWLObjectPropertyExpression nextProp = stack.pop();
    			Set<OWLObjectPropertyExpression> directSupers = 
    					this.getSuperPropertiesOf(nextProp);
    			directSupers.removeAll(superProps);
    			directSupers.remove(prop);
    			stack.addAll(directSupers);
    			superProps.addAll(directSupers);
    		}
    		//put superProps in cache
    		this.superPropertyCache.put(prop, superProps);
    	}

    	
    	LinkedHashSet<OWLObjectPropertyExpression> superPropsReflexive = 
    			new LinkedHashSet<OWLObjectPropertyExpression>();
    	superPropsReflexive.add(prop);
		superPropsReflexive.addAll(superProps);
		return superPropsReflexive;
	}
    
    /**
	 * Get the sub-relations of <code>edge</code>. This method returns 
	 * <code>OWLGraphEdge</code>s with their <code>OWLQuantifiedProperty</code>s 
	 * corresponding to the sub-properties of the properties of <code>edge</code> 
	 * (even indirect sub-properties), ordered from the more general relations 
	 * (the closest to <code>edge</code>) to the more precise relations. 
	 * The first <code>OWLGraphEdge</code> in the returned <code>Set</code> 
	 * is <code>edge</code> (reflexive method).
	 * <p>
	 * This is the opposite method of 
	 * <code>owltools.graph.OWLGraphWrapperEdges.getOWLGraphEdgeSubsumers(OWLGraphEdge)</code>, 
	 * with reflexivity added.
	 * 
	 * @param edge	A <code>OWLGraphEdge</code> for which all sub-relations 
	 * 				should be obtained.
	 * @return 		A <code>Set</code> of <code>OWLGraphEdge</code>s representing 
	 * 				the sub-relations of <code>edge</code> ordered from the more general 
	 * 				to the more precise relation, with <code>edge</code> as the first element. 
	 * 				An empty <code>Set</code> if the <code>OWLQuantifiedProperty</code>s 
	 * 				of <code>edge</code> have no sub-properties.
	 */
	public LinkedHashSet<OWLGraphEdge> getOWLGraphEdgeSubRelsReflexive(OWLGraphEdge edge) {
		return this.getOWLGraphEdgeSubRelsReflexive(edge, 0);
	}
	
	/**
	 * Similar to {@link getOWLGraphEdgeSubRels(OWLGraphEdge)}, 
	 * except the <code>OWLQuantifiedProperty</code>s of <code>edge</code> are analyzed 
	 * starting from the index <code>propIndex</code>.
	 * 
	 * @param edge 		A <code>OWLGraphEdge</code> for which sub-relations 
	 * 					should be obtained, with properties analyzed from index 
	 * 					<code>propIndex</code>
	 * @param propIndex	An <code>int</code> representing the index of the 
	 * 					<code>OWLQuantifiedProperty</code> of <code>edge</code> 
	 * 					to start the analysis with.
	 * @return 		A <code>Set</code> of <code>OWLGraphEdge</code>s representing 
	 * 				the sub-relations of <code>edge</code> ordered from the more general 
	 * 				to the more precise relation, with <code>edge</code> as the first element, 
	 * 				and with only <code>OWLQuantifiedProperty</code> starting at index 
	 * 				<code>propIndex</code>. An empty <code>Set</code> 
	 * 				if the <code>OWLQuantifiedProperty</code>s of <code>edge</code> 
	 * 				have no sub-properties.
	 */
	private LinkedHashSet<OWLGraphEdge> getOWLGraphEdgeSubRelsReflexive(OWLGraphEdge edge, 
			int propIndex) {
	    //we do not use a mechanism such as provided by OWLGraphEdge.OWLGraphEdgeSet, 
	    //first because we need a LinkedHashSet, not a HashSet, second because 
	    //by definition, subRels will not be populated with potentially equal edges.
		LinkedHashSet<OWLGraphEdge> subRels = new LinkedHashSet<OWLGraphEdge>();
		if (propIndex >= edge.getQuantifiedPropertyList().size()) {
		    subRels.add(new OWLGraphEdge(edge.getSource(), edge.getTarget(), 
		            new Vector<OWLQuantifiedProperty>(), edge.getOntology(), 
		            edge.getAxioms(), edge.getGCIFiller(), edge.getGCIRelation()));
		    return subRels;
		}
		OWLQuantifiedProperty quantProp = edge.getQuantifiedPropertyList().get(propIndex);
		LinkedHashSet<OWLQuantifiedProperty> subQuantProps = 
		        new LinkedHashSet<OWLQuantifiedProperty>();
		subQuantProps.add(quantProp);
		OWLObjectProperty prop = quantProp.getProperty();
		if (prop != null) {
		    for (OWLObjectPropertyExpression propExp : this.getSubPropertyClosureOf(prop)) {
		        if (propExp.equals(this.getDataFactory().
		                getOWLTopObjectProperty()))
		            continue;
		        if (propExp instanceof OWLObjectProperty) {
		            OWLQuantifiedProperty newQp = 
		                    new OWLQuantifiedProperty(propExp, quantProp.getQuantifier());
		            boolean isExcluded = isExcluded(newQp);
		            if (!isExcluded) {
		                subQuantProps.add(newQp);
		            }
		        }
		    }
		}
		for (OWLQuantifiedProperty subQuantProp : subQuantProps) {
		    for (OWLGraphEdge nextPropEdge : this.getOWLGraphEdgeSubRelsReflexive(edge, 
		            propIndex+1)) {
		        List<OWLQuantifiedProperty> quantProps = new Vector<OWLQuantifiedProperty>();
		        quantProps.add(subQuantProp);
		        quantProps.addAll(nextPropEdge.getQuantifiedPropertyList());

		        subRels.add(new OWLGraphEdge(edge.getSource(),edge.getTarget(),
		                quantProps, edge.getOntology(), edge.getAxioms(), 
		                edge.getGCIFiller(), edge.getGCIRelation()));
		    }
		}

		return subRels;
	}
	
    
    /**
     * Combines <code>firstEdge</code> and <code>secondEdge</code> to create a new edge 
     * from the source of <code>firstEdge</code> to the target of <code>secondEdge</code>, 
     * with properties combined in a regular way, and over super properties.
     * <p>
     * This method is similar to 
     * <code>owltools.graph.OWLGraphWrapperEdges#combineEdgePair(OWLObject, OWLGraphEdge, 
     * OWLGraphEdge, int)</code>, 
     * except it also tries to combine the <code>OWLQuantifiedProperty</code>s of the edges 
     * over super properties (see {@link #combinePropertyPairOverSuperProperties(
     * OWLQuantifiedProperty, OWLQuantifiedProperty)}, currently combines over 
     * 2 properties only). 
     * <p>
     * If one or both of the edges are GCI relations, and that their GCI fillers and/or 
     * GCI relations are related (see {@link #hasFirstEdgeMoreGeneralGCIParams(OWLGraphEdge, 
     * OWLGraphEdge)}), the combined returned edge will have the most restrictive 
     * GCI filler and GCI relation. If they are not related, the edges will not be combined.
     * 
     * @param firstEdge		A <code>OWLGraphEdge</code> that is the first edge to combine, 
     * 						its source will be the source of the new edge
     * @param secondEdge	A <code>OWLGraphEdge</code> that is the second edge to combine, 
     * 						its target will be the target of the new edge
     * @return 				A <code>OWLGraphEdge</code> resulting from the composition of 
     * 						<code>firstEdge</code> and <code>secondEdge</code>, 
     * 						with its <code>OWLQuantifiedProperty</code>s composed 
     * 						in a regular way, but also over super properties, 
     *                      and with the most restrictive GCI filler and GCI relation. 
     */
    public OWLGraphEdge combineEdgePairWithSuperPropsAndGCI(OWLGraphEdge firstEdge, 
    		OWLGraphEdge secondEdge) {
    	OWLGraphEdge combine = 
				this.combineEdgePairWithGCI(
						firstEdge.getSource(), firstEdge, secondEdge, 0);
		
		if (combine != null) {
			//in case the relations were not combined, try to combine 
			//over super properties
			//TODO: combine over more than 2 properties
			if (combine.getQuantifiedPropertyList().size() == 2) {
				OWLQuantifiedProperty combinedQp = 
						this.combinePropertyPairOverSuperProperties(
								combine.getQuantifiedPropertyList().get(0), 
								combine.getQuantifiedPropertyList().get(1));
				if (combinedQp != null) {
					//successfully combined over super properties, 
					//create a combined edge
					List<OWLQuantifiedProperty>  qps = new ArrayList<OWLQuantifiedProperty>();
					qps.add(combinedQp);
					combine = this.createMergedEdgeWithGCI(firstEdge.getSource(), 
					        firstEdge, secondEdge);
					if (combine != null) {
					    combine.setQuantifiedPropertyList(qps);
					}
				}
			}
		}
		
		return combine;
    }
    
    /**
     * Perform a combination of a pair of <code>OWLQuantifiedProperty</code>s 
     * over super properties, unlike the method 
     * {@code owltools.graph.OWLGraphWrapperEdges.combinedQuantifiedPropertyPair}. 
     * <p>
     * This method successively tries to combine {@code prop1}, or its super-properties 
     * (from the more specific to the more general), to {@code prop2}, or one of its 
     * super-property (from the more specific to the more general). It returns 
     * the first successfully combined property (meaning, the most precise property 
     * that could be combined). If no properties could be combined, this method returns 
     * {@code null}.
     * <p>
     * Note that if {@code prop1} and {@code prop2} could be combined directly, 
     * then this method should produce the same result as {@code combinedQuantifiedPropertyPair}. 
     * Otherwise, it will try to combine {@code prop1} with one of the super-properties 
     * of {@code prop2}, then one of the super-properties of {@code prop1} to 
     * {@code prop2}, or one of its super-properties, etc.
     * <p>
     * For example: 
     * <ul>
     * <li>If property r2 is transitive, and is the super property of r1, then 
     * A r1 B * B r2 C --> A r2 C
     * <li>If property r3 is transitive, and is the super property of both r1 and r2, then 
     * A r1 B * B r2 C --> A r3 C 
     * <li>If r1 * r3 --> r4, and r3 is a super-property of r2, then 
     * A r1 B * B r2 C --> A r4 C
     * </ul>
     * 
     * @param prop1 	First <code>OWLQuantifiedProperty</code> to combine
     * @param prop2		Second <code>OWLQuantifiedProperty</code> to combine
     * @return			A <code>OWLQuantifiedProperty</code> representing a combination 
     * 					of <code>prop1</code> and <code>prop2</code> over super properties. 
     * 					<code>null</code> if cannot be combined. 
     */
    OWLQuantifiedProperty combinePropertyPairOverSuperProperties(
            OWLQuantifiedProperty prop1, OWLQuantifiedProperty prop2) {
    	//local implementation of getSuperPropertyReflexiveClosureOf, to order super properties 
    	//from the more precise to the more general, with prop as the first element. 
    	//the first element is the property itself, 
    	//to check if it is a super property of the other property
    	LinkedHashSet<OWLObjectPropertyExpression> superProps1 = 
    			this.getSuperPropertyReflexiveClosureOf(prop1.getProperty());
    	LinkedHashSet<OWLObjectPropertyExpression> superProps2 = 
    			this.getSuperPropertyReflexiveClosureOf(prop2.getProperty());
    	
    	for (OWLObjectPropertyExpression p1: superProps1) {
            if (!(p1 instanceof OWLObjectProperty)) {
                continue;
            }
            OWLQuantifiedProperty newQp1 = 
                    new OWLQuantifiedProperty(p1, prop1.getQuantifier());
            if (!this.isValidQP(newQp1)) {
                continue;
            }
            for (OWLObjectPropertyExpression p2: superProps2) {
                if (!(p2 instanceof OWLObjectProperty)) {
                    continue;
                }
                OWLQuantifiedProperty newQp2 = 
                        new OWLQuantifiedProperty(p2, prop2.getQuantifier());
                if (!this.isValidQP(newQp2)) {
                    continue;
                }
                OWLQuantifiedProperty combined = 
                        combinedQuantifiedPropertyPair(newQp1, newQp2);
                if (combined != null) {
                    return combined;
                }
            }
    	}
    	return null;
    }
    
    /**
     * Checks that the {@code OWLObjectProperty} of {@code qp} is not a top object 
     * property, and that {@code qp} is not excluded (see {@link 
     * OWLGraphWrapperEdges#isExcluded(OWLQuantifiedProperty)}).
     * 
     * @param qp    The {@code OWLQuantifiedProperty} to be checked for validity.
     * @return      {@code true} if {@code qp} is valid.
     */
    private boolean isValidQP(OWLQuantifiedProperty qp) {
        //code from OWLGraphWrapperEdges.getOWLGraphEdgeSubsumers
        if (qp.getProperty().equals(
                this.getDataFactory().getOWLTopObjectProperty())) {
            return false;
        }
        if (isExcluded(qp)) {
            return false;
        }
        return true;
    }
    
    /**
     * Same method as {@link OWLGraphWrapperEdges.getOutgoingEdgesClosure(OWLObject)}, 
     * except that only the {@code OWLGraphEdge}s going to a named target are returned, 
     * and that the list of connecting edge properties are not only combined using the 
     * composition rules as usual, but also over super properties (see for instance 
     * {@link #combineEdgePairWithSuperPropsAndGCI(OWLGraphEdge, OWLGraphEdge}).
     * <p>
     * Also, redundant edges are filtered: if an edge is a sub-property of another one, 
     * only the most precise edge is returned. 
     * 
     * @param s     The {@code OWLObject} which outgoing edges start from.
     * @return      A {@code Set} of {@code OWLGraphEdge}s that represent 
     *              the graph closure originating from {@code s}, 
     *              with {@code OWLQuantifiedProperty}s combined using 
     *              standard composition rules, but also over super-properties.
     */
    public Set<OWLGraphEdge> getOutgoingEdgesNamedClosureOverSupProps(OWLObject s) {
        return this.getOutgoingEdgesNamedClosureOverSupProps(s, false);
    }
    /**
     * Similar to {@link #getOutgoingEdgesNamedClosureOverSupProps(OWLObject)} but with 
     * the OBO GCI relations also taken into account.
     * <p>
     * If both edges are GCI relations, and  their GCI fillers and/or 
     * GCI relations are related (see {@link #hasFirstEdgeMoreGeneralGCIParams(OWLGraphEdge, 
     * OWLGraphEdge)}), the combined returned edge will have the most restrictive 
     * GCI filler and GCI relation. If they are not related, the edges will not be combined. 
     * To retrieve all ancestors of an object, using also GCI relations, 
     * you should rather use {@link #getNamedAncestorsWithGCI(OWLObject)}.
     * 
     * @param s         See {@link #getOutgoingEdgesNamedClosureOverSupProps(OWLObject)}
     * @return          See {@link #getOutgoingEdgesNamedClosureOverSupProps(OWLObject)}
     */
    public Set<OWLGraphEdge> getOutgoingEdgesNamedClosureOverSupPropsWithGCI(OWLObject s) {
        return this.getOutgoingEdgesNamedClosureOverSupProps(s, true);
    }
    
    /**
     * Similar to {@link #getOutgoingEdgesNamedClosureOverSupProps(OWLObject)} with 
     * the capability of taking into account GCI relations, if {@code withGCI} 
     * is {@code true}.
     * 
     * @param s         See {@link #getOutgoingEdgesNamedClosureOverSupProps(OWLObject)}
     * @param withGCI   A {@code boolean} defining whether OBO GCI relations should also 
     *                  be taken into account. If {@code true}, they will be.
     * @return          See {@link #getOutgoingEdgesNamedClosureOverSupProps(OWLObject)}
     */
    private Set<OWLGraphEdge> getOutgoingEdgesNamedClosureOverSupProps(OWLObject s, 
            boolean withGCI) {
        
        Set<OWLGraphEdge> edges = null;
        if (withGCI) {
            edges = this.getOutgoingEdgesClosureWithGCI(s);
        } else {
            edges = this.getOutgoingEdgesClosure(s);
        }
        Set<OWLGraphEdge> edgesCombined = new OWLGraphEdgeSet();
        
        for (OWLGraphEdge e: edges) {
            //keep only edges going to a named target and not an OBO alt ID
            if (!e.isTargetNamedObject() || 
                    e.getTarget() instanceof OWLClass && this.isOboAltId((OWLClass) e.getTarget())) {
                continue;
            }
            if (LOG.isTraceEnabled()) {
                LOG.trace("Trying to combine properties for edge: " + e);
            }
            OWLGraphEdge newEdge = e;
            
            if (e.getQuantifiedPropertyList().size() > 1) {
                List<OWLQuantifiedProperty> combinedQps = new ArrayList<OWLQuantifiedProperty>();
                
                //we will try to combine a property from the original list with its predecessor, 
                //so we start the iteration at the second property of the original list.
                for (int i = 1; i < e.getQuantifiedPropertyList().size(); i++) {
                    //for the first iteration, get the first property of the original list
                    OWLQuantifiedProperty firstToCombine = e.getQuantifiedPropertyList().get(i - 1);
                    //after the first iteration, we should combine with the properties 
                    //already obtained at previous iterations. 
                    if (!combinedQps.isEmpty()) {
                        //get the latest property combined, and remove it from the List, 
                        //so that it can be replaced with a newly combined property
                        firstToCombine = combinedQps.remove(combinedQps.size() - 1);
                    }
                    
                    //OK, try to combine with the current property iterated
                    OWLQuantifiedProperty secondToCombine = e.getQuantifiedPropertyList().get(i);
                    OWLQuantifiedProperty combined = 
                            this.combinePropertyPairOverSuperProperties(
                                    firstToCombine, secondToCombine);
                    if (combined != null) {
                        combinedQps.add(combined);
                    } else {
                        //if the properties could not be combined, we put back 
                        //in combinedQps the property we removed from it, plus 
                        //the property currently iterated.
                        combinedQps.add(firstToCombine);
                        combinedQps.add(secondToCombine);
                    }
                }
                
                //combine done, let's see if we combined anything
                if (!combinedQps.equals(e.getQuantifiedPropertyList())) {
                    if (combinedQps.size() >= e.getQuantifiedPropertyList().size()) {
                        throw new AssertionError("Property composition should generate " +
                        		"less properties than in the original set of properties.");
                    }
                    
                    newEdge = new OWLGraphEdge(e.getSource(), e.getTarget(), combinedQps, 
                            e.getOntology(), e.getAxioms(), 
                            e.getGCIFiller(), e.getGCIRelation());
                    newEdge.setDistance(e.getDistance());
                }
            }
            
            if (LOG.isTraceEnabled()) {
                LOG.trace("Resulting edge: " + newEdge);
            }
            edgesCombined.add(newEdge);
        }
        
        //now, we make sure that there is no redundant combined edges, 
        //where one is a sub-property of the other, with the same target
        Set<OWLGraphEdge> filteredEdgesCombined = new OWLGraphEdgeSet();
        LOG.trace("Checking for redundancy over super-properties...");
        edge1: for (OWLGraphEdge edge1: edgesCombined) {
            if (LOG.isTraceEnabled()) {
                LOG.trace("Checking edge for redundancy: " + edge1);
            }
            edge2: for (OWLGraphEdge edge2: edgesCombined) {
                if (edge1.equals(edge2) || !edge1.getTarget().equals(edge2.getTarget())) {
                    continue edge2;
                }
                //check that edge1 is not a sub-relation of edge2
                //(the reciprocal test will be done during another iteration)
                if (this.getOWLGraphEdgeSubsumers(edge1).contains(edge2)) {
                    //invalidate edge1
                    LOG.trace("Edge redundant");
                    continue edge1;
                }
            }
            //OK, edge1 is not a sub-relation of any other edge, validated
            LOG.trace("Edge not redundant");
            filteredEdgesCombined.add(edge1);
        }
        LOG.trace("Done checking for redundancy.");
        
        return filteredEdgesCombined;
    }
    
    /**
     * Similar to {@link #getOutgoingEdgesClosure(OWLObject)}, but also considering 
     * OBO GCI relations.
     * <p>
     * Note that GCI relations are not combined when their gci_filler or gci_relation 
     * are different. The closure might then be incomplete.
     * 
     * @param s See {@link #getOutgoingEdgesClosure(OWLObject)}
     * @return  See {@link #getOutgoingEdgesClosure(OWLObject)}
     */
    public Set<OWLGraphEdge> getOutgoingEdgesClosureWithGCI(OWLObject s) {
        LOG.debug("Retrieving graph closure with GCIs for " + s);
        //try to retrieve edges from cache
        if (this.outgoingEdgesClosureWithGCIBySource == null) {
            this.outgoingEdgesClosureWithGCIBySource = 
                    new HashMap<OWLObject, Set<OWLGraphEdge>>();
        }
        Set<OWLGraphEdge> cachedEdges = this.outgoingEdgesClosureWithGCIBySource.get(s);
        if (cachedEdges != null) {
            LOG.debug("Retrieved from cache");
            //defensive copying
            return new OWLGraphEdgeSet(cachedEdges);
        }
        
        Set<OWLGraphEdge> edges = new OWLGraphEdgeSet();
        Map<OWLObject,Set<OWLGraphEdge>> visitedMap = new HashMap<OWLObject,Set<OWLGraphEdge>>();
        visitedMap.put(s, new OWLGraphEdgeSet());
        Deque<OWLGraphEdge> walkAncestors = new ArrayDeque<OWLGraphEdge>();
        
        //seed the Deque with the starting edges
        walkAncestors.addAll(this.getOutgoingEdgesWithGCI(s));
        OWLGraphEdge iteratedEdge;
        while ((iteratedEdge = walkAncestors.pollFirst()) != null) {
            OWLObject nuTarget = iteratedEdge.getTarget();
            if (LOG.isTraceEnabled()) {
                LOG.trace("Walking edge: " + iteratedEdge);
            }
            //not interested in OBO alt IDs
            if (nuTarget instanceof OWLClass && this.isOboAltId((OWLClass) nuTarget)) {
                continue;
            }
            //check for cycles
            boolean isEdgeVisited = false;
            if (visitedMap.containsKey(nuTarget)) {
                // we have potentially visited this edge before
                for (OWLGraphEdge ve : visitedMap.get(nuTarget)) {
                    //the original OWLGraphWrapperEdge code checks only the final 
                    //QuantifiedProperty, which seems to potentially discard 
                    //edges with different paths. Checking equality of visited 
                    //edges is too slow. So here, we make the QuantifiedProperties unique, 
                    //but we use each of them
                    if (new LinkedHashSet<OWLQuantifiedProperty>(
                            ve.getQuantifiedPropertyList()).equals(
                                    new LinkedHashSet<OWLQuantifiedProperty>(
                                            iteratedEdge.getQuantifiedPropertyList())) && 
                        (ve.equalsGCI(iteratedEdge) || 
                                this.hasFirstEdgeMoreGeneralGCIParams(ve, iteratedEdge))) {
                        
                        isEdgeVisited = true;
                    }
                }
            } else {
                visitedMap.put(nuTarget, new OWLGraphEdgeSet());
                visitedMap.get(nuTarget).add(iteratedEdge);
            }
            if (isEdgeVisited) {
                LOG.trace("Discarding edge because already visited");
                continue;
            }
            visitedMap.get(nuTarget).add(iteratedEdge);

            //we only want OWLNamedObjects and non OBO alt IDs
            if (iteratedEdge.getTarget() instanceof OWLNamedObject && 
                    (!(iteratedEdge.getTarget() instanceof OWLClass) || 
                            !this.isOboAltId((OWLClass) iteratedEdge.getTarget()))) {
                edges.add(iteratedEdge);
            }
            
            int nextDist = iteratedEdge.getDistance() + 1;
            for (OWLGraphEdge nextEdge: this.getOutgoingEdgesWithGCI(iteratedEdge.getTarget())) {
                OWLGraphEdge combine = this.combineEdgePairWithGCI(s, iteratedEdge, 
                        nextEdge, nextDist);
                if (combine == null) {
                    LOG.trace("Discarding edge because could not be combined");
                    continue;
                }
                walkAncestors.addLast(combine);
            }
        }
        if (LOG.isTraceEnabled()) {
            LOG.trace("Graph closure with GCIs for " + s + " retrieved: " + edges);
        }
        LOG.debug("Graph closure with GCIs retrieved.");
        this.outgoingEdgesClosureWithGCIBySource.put(s, edges);
        return edges;
    }
    
    /**
     * Lazy loads the cache for OBO gci_relations, stored as {@code OWLGraphEdge}s. 
     * Will store any GCI axiom where the sub-class is an {@code OWLObjectIntersectionOf}, 
     * with one operand being an {@code OWLClass}, and the other operand being 
     * an {@code ObjectSomeValuesFrom(OWLObjectPropertyExpression OWLClass)}. 
     * The {@code OWLGraphEdge}s are stored into {@link #gciRelationBySource}, associated 
     * to the "real" source of the edge (the {@code OWLClass} in the 
     * {@code OWLObjectIntersectionOf}), and into {@link #gciRelationByTarget}, associated 
     * to the named targets of the expanded {@code OWLGraphEdge}s. So, the current 
     * implementation assumes that {@code OWLGraphEge}s representing OBO GCI relations 
     * always have {@code OWLClass}es as source and target. 
     * <p>
     * See <a href='http://oboformat.googlecode.com/svn/trunk/doc/obo-syntax.html'>
     * Treatment of gci_relation qualifier</a> for more details.
     * 
     * @see #gciRelationBySource
     * @see #gciRelationByTarget
     */
    private void lazyLoadGCIRelCache() {
        if (this.gciRelationBySource == null) {
            
            profiler.startTaskNotify("lazyLoadGCIRelCache");
            LOG.debug("Loading GCI rel cache...");
            this.gciRelationBySource = new HashMap<OWLClass, Set<OWLGraphEdge>>();
            this.gciRelationByTarget = new HashMap<OWLClass, Set<OWLGraphEdge>>();
            
            for (OWLOntology o : this.getAllOntologies()) {
                for (OWLSubClassOfAxiom ax: o.getAxioms(AxiomType.SUBCLASS_OF)) {
                    //OBO GCI axiom using ObjectIntersectionOf
                    if (ax.getSubClass() instanceof OWLObjectIntersectionOf) {
                        OWLObjectIntersectionOf subClass = 
                                (OWLObjectIntersectionOf) ax.getSubClass();
                        //check that subclass corresponds to OWLObjectIntersectionOf(OWLClass, 
                        //ObjectSomeValuesFrom(OWLObjectPropertyExpression OWLClass))
                        if (subClass.getOperands().size() != 2) {
                            continue;
                        }
                        OWLClass source = null;
                        OWLObjectPropertyExpression gciRel = null;
                        OWLClass filler = null;
                        for (OWLClassExpression operand: subClass.getOperands()) {
                            if (operand instanceof OWLClass) {
                                source = (OWLClass) operand;
                            } else if (operand instanceof OWLObjectSomeValuesFrom && 
                                    ((OWLObjectSomeValuesFrom)operand).getFiller() 
                                        instanceof OWLClass) {
                                filler = (OWLClass) ((OWLObjectSomeValuesFrom)operand).getFiller();
                                gciRel = ((OWLObjectSomeValuesFrom)operand).getProperty();
                            }
                        }
                        if (source == null || gciRel == null || filler == null) {
                            continue;
                        }
                        
                        //valid axiom, generate OWLGraphEdges
                        OWLGraphEdge primitiveEdge = new OWLGraphEdge(source, 
                                ax.getSuperClass(), null, Quantifier.SUBCLASS_OF, o, ax, 
                                filler, gciRel);
                        if (LOG.isTraceEnabled()) {
                            LOG.trace("Primitive edge retrieved from GCI axiom " + ax + 
                                    ": " + primitiveEdge);
                        }
                        //will expand ax.getSuperClass() until we reach a named object
                        Set<OWLGraphEdge> edges = primitiveEdgeToFullEdges(primitiveEdge);
                        if (LOG.isTraceEnabled()) {
                            LOG.trace("Expanded into: " + edges);
                        }
                        
                        //store the edges associated to the "real" source (the OWLClass 
                        //in the OWLObjectIntersectionOf).
                        Set<OWLGraphEdge> edgesBySource = this.gciRelationBySource.get(source);
                        if (edgesBySource == null) {
                            edgesBySource = new OWLGraphEdgeSet();
                            this.gciRelationBySource.put(source, edgesBySource);
                        }
                        edgesBySource.addAll(edges);
                        //and also store the edges associated to the named targets
                        for (OWLGraphEdge edge: edges) {
                            OWLClass target = (OWLClass) edge.getTarget();
                            Set<OWLGraphEdge> edgesByTarget = 
                                    this.gciRelationByTarget.get(target);
                            if (edgesByTarget == null) {
                                edgesByTarget = new OWLGraphEdgeSet();
                                this.gciRelationByTarget.put(target, edgesByTarget);
                            }
                            edgesByTarget.add(edge);
                        }
                    }
                }
            }
            LOG.debug("Done loading GCI rel cache.");
            profiler.endTaskNotify("lazyLoadGCIRelCache");
        }
    }

    /**
     * Retrieve OBO GCI relations outgoing from {@code s} as a {@code Set} of {@code OWLGraphEdge}s.
     * This is similar to the method {@link OWLGraphWrapperEdges#getOutgoingEdges(OWLObject)}, 
     * but returning GCI relations only. The OBO "gci_filler" and "gci_relation" 
     * could be retrieved by calling {@link OWLGraphEdge#getGCIFiller()} and 
     * {@link OWLGraphEdge#getGCIRelation()}, respectively. 
     * <p>
     * More formally: OBO GCI relations are represented as {@code SubClassOf} axioms, 
     * where the sub-class is an {@code ObjectIntersectionOf}, with one operand 
     * being an {@code OWLClass}, and the other operand being 
     * an {@code ObjectSomeValuesFrom(ObjectPropertyExpression OWLClass)}. 
     * The {@code ObjectPropertyExpression} will be retrieved by calling 
     * {@link OWLGraphEdge#getGCIRelation()}, the associated {@code OWLClass} in the 
     * {@code ObjectSomeValuesFrom} will be retrieved by calling 
     * {@link OWLGraphEdge#getGCIFiller()}. The {@code OWLClass} operand in 
     * the {@code ObjectIntersectionOf} will be considered as the source 
     * of the {@code OWLGraphEdge}. The target will be the super-class 
     * of the {@code SubClassOf} axiom, expanded to reach a named target 
     * (as usually with methods in {@code OWLGraphWrapper}). The current 
     * implementation assumes that {@code OWLGraphEge}s representing OBO GCI relations 
     * always have {@code OWLClass}es as source and target. 
     * 
     * @param s An {@code OWLClass} for which we want to retrieve outgoing OBO GCI 
     *          relations.
     * @return  A {@code Set} of {@code OWLGraphEdge}s corresponding to GCI relations 
     *          outgoing from {@code s}.
     */
    public Set<OWLGraphEdge> getGCIOutgoingEdges(OWLClass s) {
        return this.getGCIEdges(s, true, null);
    }
    /**
     * Same as {@link #getGCIOutgoingEdges(OWLClass)}, but with a {@code Set} of 
     * {@code OWLPropertyExpression} allowing to filter the relations retrieved.
     * @param s             See {@link #getGCIOutgoingEdges(OWLClass)}.
     * @param overProps     A {@code Set} of {@code OWLPropertyExpression} allowing 
     *                      to filter the {@code OWLGraphEdge}s returned.
     * @return              See {@link #getGCIOutgoingEdges(OWLClass)}.
     * @see #getGCIOutgoingEdges(OWLClass)
     */
    public Set<OWLGraphEdge> getGCIOutgoingEdges(OWLClass s, 
            Set<OWLPropertyExpression> overProps) {
        return this.getGCIEdges(s, true, overProps);
    }
    /**
     * Retrieve OBO GCI relations incoming to {@code t} as a {@code Set} of {@code OWLGraphEdge}s.
     * See {@link #getGCIOutgoingEdges(OWLObject)} for details about OBO GCI relations, 
     * and about retrieving the associated "gci_filler" and "gci_relation".
     * 
     * @param t An {@code OWLClass} for which we want to retrieve incoming OBO GCI 
     *          relations.
     * @return  A {@code Set} of {@code OWLGraphEdge}s corresponding to GCI relations 
     *          incoming to {@code t}.
     */
    public Set<OWLGraphEdge> getGCIIncomingEdges(OWLClass t) {
        return this.getGCIEdges(t, false, null);
    }
    /**
     * Retrieve OBO GCI relations for {@code obj} as a {@code Set} of {@code OWLGraphEdge}s.
     * See {@link #getGCIOutgoingEdges(OWLObject)} for details about OBO GCI relations, 
     * and about retrieving the associated "gci_filler" and "gci_relation".
     * <p>
     * If {@code bySource} is {@code true}, edges outgoing from {@code obj} are retrieved, 
     * otherwise, edges incoming to {@code obj} are retrieved. If {@code overProperties} 
     * is not {@code null}, only the specified set of properties will be considered. Note 
     * that this does not filter for the "gci_relation" (as returned by 
     * {@link OWLGraphEdge#getGCIRelation()}), but for the actual property 
     * of the {@code OWLGraphEdge}s (as returned by 
     * {@link OWLGraphEdge#getQuantifiedPropertyList()}). 
     * <p>
     * Advanced usage notice: note that if the desired set of properties is {P},
     * and there exists a property chain Q o R --> P, then be sure to include Q and R in
     * the specified set.
     * 
     * @param obj               The {@code OWLObject} for which we want to retrieve 
     *                          OBO GCI relations
     * @param bySource          A {@code boolean} defining whether outgoing edges 
     *                          (when {@code true}) or incoming edges (when {@code false}) 
     *                          should be retrieved.
     * @param overProperties    A {@code Set} of {@code OWLPropertyExpression} allowing 
     *                          to filter the {@code OWLGraphEdge}s returned.
     * @return                  A {@code Set} of {@code OWLGraphEdge}s corresponding to 
     *                          GCI relations for {@code obj}.
     */
    private Set<OWLGraphEdge> getGCIEdges(OWLClass obj, boolean bySource, 
            Set<OWLPropertyExpression> overProperties) {
        lazyLoadGCIRelCache();
        
        Set<OWLGraphEdge> cachedEdges = null;
        if (bySource) {
            cachedEdges = this.gciRelationBySource.get(obj);
        } else {
            cachedEdges = this.gciRelationByTarget.get(obj);
        }
        if (LOG.isTraceEnabled()) {
            LOG.trace("GCI edges retrieved for " + obj + ": " + cachedEdges);
        }
        if (cachedEdges != null) {
            //defensive copying
            Set<OWLGraphEdge> edges = new OWLGraphEdgeSet(cachedEdges);
            filterEdges(edges, overProperties);
            return edges;
        } 

        return new OWLGraphEdgeSet();
    }
    
    /**
     * Similar to {@link OWLGraphWrapperEdges#getOutgoingEdges(OWLObject)}, but the returned 
     * {@code Set} also includes OBO GCI outgoing edges (see 
     * {@link #getGCIOutgoingEdges(OWLClass)}).
     * 
     * @param s     An {@code OWLObject} for which we want to retrieve outgoing edges, 
     *              including OBO GCI relations.
     * @return      A {@code Set} of {@code OWLGraphEdge}s outgoing from {@code s}, 
     *              including OBO GCI relations.
     * @see #getOutgoingEdgesWithGCI(OWLObject, Set)
     * @see #getGCIOutgoingEdges(OWLClass)
     */
    public Set<OWLGraphEdge> getOutgoingEdgesWithGCI(OWLObject s) {
        return getOutgoingEdgesWithGCI(s, null);
    }

    /**
     * Similar to {@link OWLGraphWrapperEdges#getOutgoingEdges(OWLObject, Set)}, but the returned 
     * {@code Set} also includes OBO GCI outgoing edges (see 
     * {@link #getGCIOutgoingEdges(OWLClass)}).
     * 
     * @param s             An {@code OWLObject} for which we want to retrieve outgoing edges, 
     *                      including OBO GCI relations.
     * @param overProps     A {@code Set} of {@code OWLPropertyExpression} allowing 
     *                      to filter the {@code OWLGraphEdge}s returned.
     * @return      A {@code Set} of {@code OWLGraphEdge}s outgoing from {@code s}, 
     *              including OBO GCI relations.
     * @see #getGCIOutgoingEdges(OWLClass)
     */
    public Set<OWLGraphEdge> getOutgoingEdgesWithGCI(OWLObject s, 
            Set<OWLPropertyExpression> overProperties) {
        Set<OWLGraphEdge> edges = super.getOutgoingEdges(s, overProperties);
        if (s instanceof OWLClass) {
            edges.addAll(getGCIOutgoingEdges((OWLClass) s, overProperties));
        }
        return edges;
    }
    
    /**
     * Similar to {@link OWLGraphWrapperEdges#getIncomingEdges(OWLObject)}, but the returned 
     * {@code Set} also includes OBO GCI incoming edges (see 
     * {@link #getGCIIncomingEdges(OWLClass)}).
     * 
     * @param t     An {@code OWLObject} for which we want to retrieve incoming edges, 
     *              including OBO GCI relations.
     * @return      A {@code Set} of {@code OWLGraphEdge}s incoming to {@code t}, 
     *              including OBO GCI relations.
     * @see #getGCIIncomingEdges(OWLClass)
     */
    public Set<OWLGraphEdge> getIncomingEdgesWithGCI(OWLObject t) {
        Set<OWLGraphEdge> edges = super.getIncomingEdges(t);
        if (t instanceof OWLClass) {
            edges.addAll(getGCIIncomingEdges((OWLClass) t));
        }
        return edges;
    }
    
    /**
     * Returns either the ancestors or the descendants of an {@code OWLObject} 
     * through both classical relations an OBO GCI relations. Ancestors will be returned 
     * if {@code ancestors} is {@code true}, otherwise, descendants will be returned. 
     * Only {@code OWLNamedObject} ancestors or descendants are returned.
     * 
     * @param x         An {@code OWLObject} for which we want to retrieve either the ancestors, 
     *                  or the descendants.
     * @param ancestors A {@code boolean} defining whether ancestors should be retrieved 
     *                  (if {@code true}), or descendants (if {@code false}).
     * @param overProps A {@code Set} of {@code OWLPropertyExpression} allowing to filter 
     *                  the relations considered to retrieve ancestors.
     * @return  A {@code Set} of {@code OWLNamedObject}es that are either the named ancestors 
     *          (if {@code ancestors} is {@code true}) or the named descendants 
     *          (if {@code ancestors} is {@code false}) of {@code x} through 
     *          both classical and OBO GCI relations.
     */
    private Set<OWLNamedObject> getNamedGCIRelatives(OWLObject x, boolean ancestors, 
            @SuppressWarnings("rawtypes") Set<OWLPropertyExpression> overProps) {
        Set<OWLNamedObject> relatives = new HashSet<OWLNamedObject>();
        Deque<OWLObject> walkRelatives = new ArrayDeque<OWLObject>();
        //seed the Deque with the starting OWLClass
        walkRelatives.addFirst(x);
        OWLObject iteratedRelative;
        while ((iteratedRelative = walkRelatives.pollFirst()) != null) {
            Set<OWLGraphEdge> edges = null;
            if (ancestors) {
                edges = this.getOutgoingEdgesWithGCI(iteratedRelative);
            } else {
                edges = this.getIncomingEdgesWithGCI(iteratedRelative);
            }
            filterEdges(edges, overProps);
            for (OWLGraphEdge edge: edges) {
                OWLObject relative = null;
                if (ancestors) {
                    relative = edge.getTarget();
                } else {
                    relative = edge.getSource();
                }
                //protect against cycles
                if (relatives.contains(relative)) {
                    continue;
                }
                //not interested in OBO alt IDs
                if (relative instanceof OWLClass && this.isOboAltId((OWLClass) relative)) {
                    continue;
                }
                //we only want OWLNamedObjects and non OBO alt IDs
                if (relative instanceof OWLNamedObject) {
                    relatives.add((OWLNamedObject) relative);
                }
                walkRelatives.addLast(relative);
            }
        }
        
        return relatives;
    }
    
    /**
     * Similar to {@link OWLGraphWrapperEdges#getNamedAncestors(OWLObject)} but also 
     * considering GCI relations.
     * @param sourceObject  An {@code OWLObject} for which we want to retrieve ancestors 
     *                      through classical relations and through OBO GCI relations.
     * @return  A {@code Set} of {@code OWLNamedObject}s that are ancestors of 
     *          {@code sourceObject} through classical relations and through OBO GCI relations.
     * @see #getNamedAncestorsWithGCI(OWLObject, Set)
     * @see #getOWLClassAncestorsWithGCI(OWLObject, Set)
     */
    public Set<OWLNamedObject> getNamedAncestorsWithGCI(OWLObject sourceObject) {
        return this.getNamedGCIRelatives(sourceObject, true, null);
    }
    /**
     * Similar to {@link #getNamedAncestorsWithGCI(OWLObject, Set)} but allowing to filter 
     * the relations considered. 
     * @param sourceObject  An {@code OWLObject} for which we want to retrieve ancestors 
     *                      through classical relations and through OBO GCI relations.
     * @param overProps     A {@code Set} of {@code OWLPropertyExpression} allowing to filter 
     *                      the relations considered to retrieve ancestors.
     * @return  A {@code Set} of {@code OWLObject}s that are ancestors of 
     *          {@code sourceObject} through classical relations and through OBO GCI relations, 
     *          filtered using {@code overProps}.
     * @see #getNamedAncestorsWithGCI(OWLObject)
     * @see #getOWLClassAncestorsWithGCI(OWLObject)
     */
    public Set<OWLNamedObject> getNamedAncestorsWithGCI(OWLObject sourceObject, 
            @SuppressWarnings("rawtypes") Set<OWLPropertyExpression> overProps) {
        return this.getNamedGCIRelatives(sourceObject, true, overProps);
    }
    
    /**
     * Similar to {@link #getNamedAncestorsWithGCI(OWLObject)} but returning only 
     * {@code OWLClass}es.
     * @param sourceObject  An {@code OWLObject} for which we want to retrieve ancestors 
     *                      through classical relations and through OBO GCI relations.
     * @return  A {@code Set} of {@code OWLClass}s that are ancestors of 
     *          {@code sourceObject} through classical relations and through OBO GCI relations.
     */
    public Set<OWLClass> getOWLClassAncestorsWithGCI(OWLObject sourceObject) {
        Set<OWLClass> ancestors = new HashSet<OWLClass>();
        for (OWLNamedObject anc: this.getNamedAncestorsWithGCI(sourceObject)) {
            if (anc instanceof OWLClass) {
                ancestors.add((OWLClass) anc);
            }
        }
        return ancestors;
    }

    /**
     * Similar to {@link #getOWLClassDirectDescendants(OWLClass)} but also considering GCI relations.
     * @param parentClass   An {@code OWLClass} for which we want to retrieve direct descendants 
     *                      through classical relations and through OBO GCI relations.
     * @return  A {@code Set} of {@code OWLClass}s that are direct descendants of {@code parentClass} 
     *          through classical relations and through OBO GCI relations.
     */
    public Set<OWLClass> getOWLClassDirectDescendantsWithGCI(OWLClass parentClass) {
        Set<OWLClass> directDescendants = new HashSet<OWLClass>();
        for (OWLGraphEdge e: this.getIncomingEdgesWithGCI(parentClass)) {
            if (e.getSource() instanceof OWLClass) {
                directDescendants.add((OWLClass) e.getSource());
            }
        }
        return directDescendants;
    }
    
    /**
     * Similar to {@link #getOWLClassDescendants(OWLClass)} but also considering GCI relations.
     * @param parentClass   An {@code OWLClass} for which we want to retrieve descendants 
     *                      through classical relations and through OBO GCI relations.
     * @return  A {@code Set} of {@code OWLClass}s that are descendants of {@code parentClass} 
     *          through classical relations and through OBO GCI relations.
     */
    public Set<OWLClass> getOWLClassDescendantsWithGCI(OWLClass parentClass) {
        return this.getOWLClassDescendantsWithGCI(parentClass, null);
    }
    /**
     * Similar to {@link #getOWLClassDescendantsWithGCI(OWLObject)} but allowing to filter 
     * the relations considered. 
     * @param parentClass   An {@code OWLClass} for which we want to retrieve descendants 
     *                      through classical relations and through OBO GCI relations.
     * @param overProps     A {@code Set} of {@code OWLPropertyExpression} allowing to filter 
     *                      the relations considered to retrieve descendants.
     * @return  A {@code Set} of {@code OWLClass}s that are descendants of {@code parentClass} 
     *          through classical relations and through OBO GCI relations, 
     *          filtered using {@code overProps}.
     */
    public Set<OWLClass> getOWLClassDescendantsWithGCI(OWLClass parentClass, 
            @SuppressWarnings("rawtypes") Set<OWLPropertyExpression> overProps) {
        Set<OWLClass> descendants = new HashSet<OWLClass>();
        for (OWLNamedObject desc: this.getNamedGCIRelatives(parentClass, false, overProps)) {
            if (desc instanceof OWLClass) {
                descendants.add((OWLClass) desc);
            }
        }
        return descendants;
    }
    
    /**
     * Same as {@link OWLGraphWrapperEdges#combineEdgePair(OWLObject, OWLGraphEdge, 
     * OWLGraphEdge, int)} except that the GCI filler an GCI relation of the edges 
     * are taken into account.
     * <p>
     * If both edges are GCI relations, and  their GCI fillers and/or 
     * GCI relations are related (see {@link #hasFirstEdgeMoreGeneralGCIParams(OWLGraphEdge, 
     * OWLGraphEdge)}), the combined returned edge will have the most restrictive 
     * GCI filler and GCI relation. If they are not related, the edges will not be combined.
     * 
     * @param s             See {@code combineEdgePair} method.
     * @param ne            See {@code combineEdgePair} method.
     * @param extEdge       See {@code combineEdgePair} method.
     * @param nextDist      See {@code combineEdgePair} method.
     * @return              See {@code combineEdgePair} method.
     * @see #combineEdgePair(OWLObject, OWLGraphEdge, OWLGraphEdge, int)
     */
    public OWLGraphEdge combineEdgePairWithGCI(OWLObject s, OWLGraphEdge ne, 
            OWLGraphEdge extEdge, int nextDist) {
        //System.out.println("combing edges: "+s+" // "+ne+ " * "+extEdge);
        // Create an edge with no edge labels; we will fill the label in later.
        OWLGraphEdge mergedEdge = this.createMergedEdgeWithGCI(s, ne, extEdge);
        if (mergedEdge == null) 
            return null;
        if (this.combineEdgePair(mergedEdge, 
                ne.getQuantifiedPropertyList(), extEdge.getQuantifiedPropertyList(), 
                nextDist)) {
            return mergedEdge;
        }
        return null;
    }
    
    /**
     * Create a new {@code OWLGraphEdge} going from {@code source}, to the target of 
     * {@code targetEdge}, by merging the underling {@code OWLAxiom}s of {@code sourceEdge} 
     * and {@code targetEdge} (as returned by {@link OWLGraphEdge#getAxioms()}), 
     * and setting the {@code OWLOntology} of this new edge with the one of either 
     * {@code sourceEdge} or {@code targetEdge}, as well as their gci_filler and gi_relation.
     * {@code OWLQuantifiedProperty}s are not set. 
     * <p>
     * If both edges are GCI relations, and  their GCI fillers and/or 
     * GCI relations are related (see {@link #hasFirstEdgeMoreGeneralGCIParams(OWLGraphEdge, 
     * OWLGraphEdge)}), the combined returned edge will have the most restrictive 
     * GCI filler and GCI relation. If they are not related, the edges will not be combined.
     * 
     * @param source       The {@code OWLObject} which this new edge will originate from.
     * @param sourceEdge   The {@code OWLGraphEdge} to merge with {@code targetEdge}.
     * @param targetEdge   The {@code OWLGraphEdge} going to the target of the new edge 
     *                     created, and to be merged with {@code sourceEdge}.
     * @return             A newly created {@code OWLGraphEdge}, 
     *                     with no {@code OWLQuantifiedProperty} set.
     */
    private OWLGraphEdge createMergedEdgeWithGCI(OWLObject source, OWLGraphEdge sourceEdge, 
            OWLGraphEdge targetEdge) {
        
        OWLClass gciFiller = null;
        OWLObjectPropertyExpression gciRel= null;
        if (sourceEdge.equalsGCI(targetEdge) || 
                this.hasFirstEdgeMoreGeneralGCIParams(targetEdge, sourceEdge)) {
            //use GCI filler and rel from sourceEdge if GCI parameters are equal, 
            //of if GCI parameters of sourceEdge are more restrictive
            gciFiller = sourceEdge.getGCIFiller();
            gciRel = sourceEdge.getGCIRelation();
        } else if (this.hasFirstEdgeMoreGeneralGCIParams(sourceEdge, targetEdge)) {
            //or if the GCI params of targetEdge are more restrictive, use them 
            gciFiller = targetEdge.getGCIFiller();
            gciRel = targetEdge.getGCIRelation();
        } else {
            //otherwise, GCI params are not related and the edges cannot be combined
            return null;
        }
        
        //merges the underlying axioms of these edges
        Set<OWLAxiom> axioms = new HashSet<OWLAxiom>(sourceEdge.getAxioms());
        axioms.addAll(targetEdge.getAxioms());
        
        return new OWLGraphEdge(source, targetEdge.getTarget(), 
                (sourceEdge.getOntology() != null ? 
                        sourceEdge.getOntology() : targetEdge.getOntology()), 
                axioms, gciFiller, gciRel);
    }
    
    /**
     * Determines whether the GCI parameters of the GCI relation {@code firstEdge}
     * are more general than the GCI parameters of the GCI relation {@code otherEdge}. 
     * <p>
     * Note that if the GCI parameters ({@link OWLGraphEdge#getGCIFiller()} and 
     * {@link OWLGraphEdge#getGCIRelation()}) of {@code firstEdge} and of {@code otherEdge} 
     * are equal, this method will return {@code false} (use 
     * {@link OWLGraphEdge#equalsGCI(OWLGraphEdge)} instead). As a result, 
     * this method will also return {@code false} if none of the arguments are GCI relations.
     * <p>
     * For this method to return {@code true}, one of the parameters of {@code firstEdge} 
     * has to be more general than the same parameter of {@code otherEdge}, while 
     * the other parameter of {@code firstEdge} is equal or more general than 
     * the same parameter of {@code otherEdge}. 
     * <p>
     * Note that the order of the parameters is important (if 
     * {@code hasFirstEdgeMoreGeneralGCI(edge1, edge2)} returns {@code true}, 
     * {@code hasFirstEdgeMoreGeneralGCI(edge2, edge1)} will return {@code false}).
     * 
     * @param firstEdge An {@code OWLGraphEdge} for which we want to determine whether 
     *                  its GCI parameters are more general than those of {@code otherEdge}.
     * @param otherEdge An {@code OWLGraphEdge} for which we want to determine GCI parameter 
     *                  inclusion into those of {@code firstEdge}.
     * @return     {@code true} if {@code firstEdge} has more general GCI parameters 
     *             than those of {@code otherEdge}.
     */
    public boolean hasFirstEdgeMoreGeneralGCIParams(OWLGraphEdge firstEdge, 
            OWLGraphEdge otherEdge) {
        if (firstEdge == null || otherEdge == null) 
            return false;
        if (firstEdge.equalsGCI(otherEdge)) 
            return false;
        //if first edge is not a GCI, otherEdge has to be a GCI (previous equalsGCI test).
        //so, first edge is more general in any case.
        if (!firstEdge.isGCI()) 
            return true;
        //same logic the other way around
        if (!otherEdge.isGCI())
            return false;
        
        //at this point, both firstEdge and otherEdge are GCI relations, 
        //but with different gci fillers and/or gci relations. Throw AssertionErrors,  
        //as the logic afterwards is completely based on these assertions, and we blindly 
        //return true at the end.
        if (firstEdge.getGCIFiller() == null || firstEdge.getGCIRelation() == null || 
                otherEdge.getGCIFiller() == null || otherEdge.getGCIRelation() == null) 
            throw new AssertionError("GCI parameters of the compared edges cannot be null " +
            		"at this point. First edge: " + firstEdge + " - Other edge: " + otherEdge);
        if (firstEdge.getGCIFiller().equals(otherEdge.getGCIFiller()) && 
                firstEdge.getGCIRelation().equals(otherEdge.getGCIRelation()))
            throw new AssertionError("GCI fillers and relations of the compared edges " +
            		"cannot be both equal at this point. First edge: " + firstEdge + 
            		" - Other edge: " + otherEdge);
        
        //Check whether the gci filler and/or relation of firstEdge is equal to 
        //or more general than the gci filler and/or relation of otherEdge
        
        if (!firstEdge.getGCIRelation().equals(otherEdge.getGCIRelation()) && 
                !this.getSuperPropertyClosureOf(otherEdge.getGCIRelation()).contains(
                        firstEdge.getGCIRelation())) 
            return false;
            
        if (!firstEdge.getGCIFiller().equals(otherEdge.getGCIFiller()) && 
                !this.getAncestorsThroughIsA(otherEdge.getGCIFiller()).contains(
                        firstEdge.getGCIFiller())) 
            return false;
        
        return true;
    }
    

    
    /**
     * Retrieve {@code OWLClass} ancestors of {@code x} only using "is_a" relations 
     * ({@code SubClassOf}).
     * 
     * @param x An {@code OWLObject} for which we want to retrieve {@code OWLClass} ancestors 
     *          through "is_a" relations, even indirect.
     * @return  A {@code Set} of {@code OWLClass}es that are the ancestors of {@code x} 
     *          through "is_a" relations.
     * @see #getDescendantsThroughIsA(OWLObject)
     */
    public Set<OWLClass> getAncestorsThroughIsA(OWLObject x) {
        return this.getRelativesThroughIsA(x, true);
    }
    /**
     * Retrieve {@code OWLClass} descendants of {@code x} only using "is_a" relations 
     * ({@code SubClassOf}).
     * 
     * @param x An {@code OWLObject} for which we want to retrieve {@code OWLClass} descendants 
     *          through "is_a" relations, even indirect.
     * @return  A {@code Set} of {@code OWLClass}es that are the descendants of {@code x} 
     *          through "is_a" relations.
     * @see #getAncestorsThroughIsA(OWLObject)
     */
    public Set<OWLClass> getDescendantsThroughIsA(OWLObject x) {
        return this.getRelativesThroughIsA(x, false);
    }
    /**
     * Retrieve {@code OWLClass} ancestors or descendants of {@code x} only using "is_a" 
     * relations ({@code SubClassOf). If {@code ancestors} is {@code true}, ancestors 
     * will be retrieved, otherwise, decendants will be retrieved. 
     * 
     * @param x         An {@code OWLObject} for which we want to retrieve 
     *                  {@code OWLClass} ancestors or descendants through "is_a" relations, 
     *                  even indirect.
     * @param ancestors A {@code boolean} defining whether ancestors or descendants 
     *                  should be retrieved. If {@code true}, ancestors will be retrieved, 
     *                  otherwise, descendants. 
     * @return  A {@code Set} of {@code OWLClass}es that are the ancestors or descendants 
     *          of {@code x} through "is_a" relations.
     */
    private Set<OWLClass> getRelativesThroughIsA(OWLObject x, boolean ancestors) {
        
        Set<OWLClass> relatives = new HashSet<OWLClass>();
        //protect against cycles
        Set<OWLObject> visited = new HashSet<OWLObject>();
        //avoid recursivity by using a Deque
        Deque<OWLObject> walkAncestors = new ArrayDeque<OWLObject>();
        //seed the Deque with the starting OWLObject
        walkAncestors.addFirst(x);
        OWLObject iteratedRelative;
        while ((iteratedRelative = walkAncestors.pollFirst()) != null) {
            Set<OWLGraphEdge> edges = new HashSet<OWLGraphEdge>();
            if (ancestors) {
                edges = this.getOutgoingEdgesWithGCI(iteratedRelative);
            } else {
                edges = this.getIncomingEdgesWithGCI(iteratedRelative);
            }
            for (OWLGraphEdge edge: edges) {
                //if not an is_a relation, continue
                if (edge.getSingleQuantifiedProperty().getProperty() != null || 
                        !edge.getSingleQuantifiedProperty().isSubClassOf()) {
                    continue;
                }
                
                OWLObject relative = null;
                if (ancestors) {
                    relative = edge.getTarget();
                } else {
                    relative = edge.getSource();
                }
                        
                //protect against cycles
                if (visited.contains(relative)) {
                    continue;
                }
                visited.add(relative);
                //we only want OWLClasses
                if (relative instanceof OWLClass) {
                    relatives.add((OWLClass) relative);
                }
                walkAncestors.addLast(relative);
            }
        }
        
        return relatives;
    }
    
    @Override
    public void clearCachedEdges() {
        super.clearCachedEdges();
        this.gciRelationBySource = null;
        this.gciRelationByTarget = null;
        this.outgoingEdgesClosureWithGCIBySource = null;
    }
    
    /**
     * Translates the source of an {@code OWLGraphEdge} into an {@code OWLClassExpression} 
     * (but, as the method {@link OWLGraphEdge#getSource()} returns an {@code OWLObject}, 
     * this method also returns an {@code OWLObject}). This is the equivalent method 
     * to {@link OWLGraphWrapperEdges#edgeToTargetExpression(OWLGraphEdge)}, 
     * but for the source.
     * <p>
     * This is useful when an {@code OWLGraphEdge} corresponds to an OBO gci_relation 
     * ({@link OWLGraphEdge#isGCI()} returns {@code true}). In that case, the returned value 
     * is an {@code OWLObjectIntersectionOf}. If it is not a GCI, the returned value 
     * is equal to {@link OWLGraphEdge#getSource()}.
     * 
     * @param e The {@code OWLGraphEdge} for which we want to translate the source 
     *          into an {@code OWLClassExpression}.
     * @return  An {@code OWLObject} corresponding to the source of {@code e}.
     */
    public OWLObject edgeToSourceExpression(OWLGraphEdge e) {
        if (!e.isGCI()) {
            return e.getSource();
        }
        OWLDataFactory factory = e.getOntology().getOWLOntologyManager().getOWLDataFactory();
        return factory.getOWLObjectIntersectionOf((OWLClassExpression) e.getSource(), 
                factory.getOWLObjectSomeValuesFrom(e.getGCIRelation(), e.getGCIFiller()));
    }

    
    //***************************************
    // CONVENIENT METHODS TO GET OWLCLASSES
    //***************************************
	/**
     * Get all <code>OWLClass</code>es from all ontologies, 
     * that are neither top entity (owl:thing), nor bottom entity (owl:nothing), 
     * nor deprecated ({@link OWLGraphWrapperExtended#isObsolete(OWLObject)} 
     * returns {@code false}), nor an OBO alt ID.
     * 
     * @return 	a <code>Set</code> containing all "real" <code>OWLClass</code>es 
     *          from all ontologies.
     */
    public Set<OWLClass> getAllRealOWLClasses() {
    	//maybe classes can be shared between ontologies?
    	//use a Set to check
    	Set<OWLClass> allClasses = new HashSet<OWLClass>();
    	for (OWLOntology ont : this.getAllOntologies()) {
			for (OWLClass cls: ont.getClassesInSignature()) {
			    if (this.isRealClass(cls)) {
				    allClasses.add(cls);
			    }
			}
		}
    	return allClasses;
    }

    /**
     * Get only the <code>OWLClass</code>es from the {@code OWLOntology} returned 
     * by {@link #getSourceOntology()}, that are neither top entity (owl:thing), 
     * nor bottom entity (owl:nothing), nor deprecated ({@link 
     * OWLGraphWrapperExtended#isObsolete(OWLObject)} returns {@code false}), 
     * nor an OBO alt ID.
     * 
     * @return  a <code>Set</code> of <code>OWLClass</code>es from the source ontology, 
     *          owl:thing, owl:nothing, deprecated classes excluded.
     */
    public Set<OWLClass> getAllRealOWLClassesFromSource() {
        Set<OWLClass> allClasses = new HashSet<OWLClass>();
        for (OWLClass cls: this.getSourceOntology().getClassesInSignature()) {
            if (this.isRealClass(cls)) {
                allClasses.add(cls);
            }
        }
        return allClasses;
    }
    
    /**
     * Return the <code>OWLClass</code>es root of any ontology 
     * (<code>OWLClass</code>es with no outgoing edges as returned by 
     * {OWLGraphWrapperEdges#getOutgoingEdgesWithGCI(OWLObject)}), and not deprecated 
     * ({@link OWLGraphWrapperExtended#isObsolete(OWLObject)} returns {@code false})).
     * 
     * @return	A <code>Set</code> of <code>OWLClass</code>es that are 
     * 			the roots of any ontology.
     */
    public Set<OWLClass> getOntologyRoots() {
    	return getOntologyRoots(null);
    }
    /**
     * Return the <code>OWLClass</code>es root of any ontology over the specified 
     * {@code OWLPropertyExpression}s (<code>OWLClass</code>es with no outgoing edges 
     * of the specified type, as returned by 
     * {OWLGraphWrapperEdges#getOutgoingEdgesWithGCI(OWLObject, Set)}), and not deprecated 
     * ({@link OWLGraphWrapperExtended#isObsolete(OWLObject)} returns {@code false}); 
     * edges going to obsolete classes are not taken into account).
     * <p>
     * Filtering roots using {@code overProperties} allow to ask question such as: 
     * what are the roots of the ontology according only to {@code is_a} 
     * and {@code part_of} relations.
     * 
     * @param overProps     A {@code Set} of {@code OWLPropertyExpression} allowing 
     *                      to filter the roots returned.
     * @return  A <code>Set</code> of <code>OWLClass</code>es that are 
     *          the roots of any ontology over the provided {@code OWLPropertyExpression}s.
     */
    public Set<OWLClass> getOntologyRoots(Set<OWLPropertyExpression> overProperties) {
        Set<OWLClass> ontRoots = new HashSet<OWLClass>();
        for (OWLOntology ont: this.getAllOntologies()) {
            cls: for (OWLClass cls: ont.getClassesInSignature()) {
                if (this.isRealClass(cls)) {
                    for (OWLGraphEdge edge: this.getOutgoingEdgesWithGCI(cls, overProperties)) {
                        //if the edge does not go to the class itself (cycle), and 
                        //does not go to an obsolete class, it is a valid edge 
                        //and cls is not a root, continue.
                        if (!edge.getTarget().equals(cls) && 
                                this.isRealClass(edge.getTarget())) {
                            continue cls;
                        }
                    }
                    ontRoots.add(cls);
                }
            }
        }
        return ontRoots;
    }
    
    /**
     * Return the <code>OWLClass</code>es leaves of any ontology 
     * (<code>OWLClass</code>es with no incoming edges as returned by 
     * {OWLGraphWrapperEdges#getIncomingEdgesWithGCI(OWLObject)}), and not deprecated 
     * ({@link OWLGraphWrapperExtended#isObsolete(OWLObject)} returns {@code false}; 
     * edges incoming from an obsolete class are not considered)
     * 
     * @return  A <code>Set</code> of <code>OWLClass</code>es that are 
     *          the leaves of any ontology.
     */
    //TODO: DRY, almost same code as getOntologyRoots
    public Set<OWLClass> getOntologyLeaves() {
        Set<OWLClass> ontLeaves = new HashSet<OWLClass>();
        for (OWLOntology ont: this.getAllOntologies()) {
            cls: for (OWLClass cls: ont.getClassesInSignature()) {
                if (this.isRealClass(cls)) {
                    for (OWLGraphEdge edge: this.getIncomingEdgesWithGCI(cls)) {
                        //if the edge does not come from the class itself (cycle), and 
                        //does not come from an obsolete class, it is a valid edge 
                        //and cls is not a leaf, continue.
                        if (!edge.getSource().equals(cls) && 
                                this.isRealClass(edge.getSource())) {
                            continue cls;
                        }
                    }
                    ontLeaves.add(cls);
                }
            }
        }
        return ontLeaves;
    }
    
    /**
     * Return the <code>OWLClass</code>es descendant of <code>parentClass</code>.
     * This method is the same than 
     * <code>owltools.graph.OWLGraphWrapperEdges.getDescendants(OWLObject)</code>, 
     * except it returns only <code>OWLClass</code>es.
     * 
     * @param parentClass 
     * @return 	A <code>Set</code> of <code>OWLClass</code>es being the descendants 
     * 			of <code>parentClass</code>.
     */
    public Set<OWLClass> getOWLClassDescendants(OWLClass parentClass) {
    	Set<OWLClass> descendants = new HashSet<OWLClass>();
		for (OWLObject descendant: 
			    this.getDescendants(parentClass)) {
			if (this.isRealClass(descendant)) {
				descendants.add((OWLClass) descendant);
			}
		}
		
		return descendants;
    }
    /**
     * Return the <code>OWLClass</code>es directly descendant of <code>parentClass</code>.
     * This method returns all sources of all edges incoming to <code>parentClass</code>, 
     * that are <code>OWLClass</code>es.
     * 
     * @param parentClass   The {@code OWLClass} for which we want the direct 
     *                      descendant {@code OWLClass}es
     * @return 	A <code>Set</code> of <code>OWLClass</code>es being the direct descendants 
     * 			of <code>parentClass</code>.
     * @see owltools.graph.OWLGraphWrapperEdges#getIncomingEdges(OWLObject)
     */
    public Set<OWLClass> getOWLClassDirectDescendants(OWLClass parentClass) {
    	
    	Set<OWLClass> directDescendants = new HashSet<OWLClass>();
    	for (OWLGraphEdge incomingEdge: 
    		    this.getIncomingEdges(parentClass)) {

    		OWLObject directDescendant = incomingEdge.getSource();
    		if (this.isRealClass(directDescendant)) { 
    			directDescendants.add((OWLClass) directDescendant);
    		}
    	}
		
    	return directDescendants;
    }
    /**
     * Return the <code>OWLClass</code>es that are direct parent of <code>subClass</code>.
     * This method returns all sources of all edges incoming to <code>subClass</code>, 
     * that are <code>OWLClass</code>es.
     * 
     * @param subClass 
     * @return  A <code>Set</code> of <code>OWLClass</code>es being the direct parents 
     *          of <code>subClass</code>.
     * @see owltools.graph.OWLGraphWrapperEdges#getOutgoingEdges(OWLObject)
     */
    public Set<OWLClass> getOWLClassDirectAncestors(OWLClass subClass) {
        
        Set<OWLClass> directParents = new HashSet<OWLClass>();
        for (OWLGraphEdge outgoingEdge: 
                this.getOutgoingEdges(subClass)) {

            OWLObject directParent = outgoingEdge.getTarget();
            if (this.isRealClass(directParent)) { 
                directParents.add((OWLClass) directParent);
            }
        }
        
        return directParents;
    }
    
    
    /**
     * Return the <code>OWLClass</code>es ancestor of <code>sourceClass</code>.
     * This method is the same than 
     * <code>owltools.graph.OWLGraphWrapperEdges.getAncestors(OWLObject)</code>, 
     * except it returns only the ancestor that are <code>OWLClass</code>es.
     * 
     * @param sourceClass 
     * @return 	A <code>Set</code> of <code>OWLClass</code>es being the ancestors 
     * 			of <code>sourceClass</code>.
     */
    public Set<OWLClass> getOWLClassAncestors(OWLClass sourceClass) {
    	
    	Set<OWLClass> ancestors = new HashSet<OWLClass>();
		for (OWLObject ancestor: 
			    this.getAncestors(sourceClass)) {
			if (this.isRealClass(ancestor)) {
				ancestors.add((OWLClass) ancestor);
			}
		}
		
		return ancestors;
    }
    
    /**
     * Determines that {@code object} is an {@code OWLClass} that is neither owl:thing, 
     * nor owl:nothing, and that it is not deprecated 
     * ({@link OWLGraphWrapperExtended#isObsolete(OWLObject)} returns {@code false}) 
     * and that is not an OBO alt ID.
     * 
     * @param object    An {@code OWLObject} to be checked to be an {@code OWLClass} 
     *                  actually used.
     * @return          {@code true} if {@code object} is an {@code OWLClass} that is not 
     *                  owl:thing, nor owl:nothing, and is not deprecated.
     */
    public boolean isRealClass(OWLObject object) {
        return (object instanceof OWLClass) && !isOboAltId((OWLClass) object) && 
                !isObsolete(object) && !getIsObsolete(object) && 
                !object.isTopEntity() && !object.isBottomEntity();
    }
}
