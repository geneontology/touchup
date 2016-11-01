package org.bbop.phylo.gaf.parser;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.lang3.StringUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.bbop.phylo.model.Bioentity;
import org.bbop.phylo.model.GeneAnnotation;

public class BuilderTools {

	static String handleTaxonPrefix(String s) {
		if (s != null && !s.isEmpty()) {
			int colPos = s.indexOf(':');
			StringBuilder sb = new StringBuilder(TaxonTools.NCBI);
			if (colPos > 0) {
				sb.append(s.substring(colPos+1));
			}
			else {
				sb.append(s);
			}
			return sb.toString();
		}
		return s;
	}
	
	public static String removePrefix(String s, char marker) {
		int pos = s.indexOf(marker);
		if (pos > 0) {
			if ((pos + 1) < s.length()) {
				pos += 1;
			}
			return s.substring(pos);
		}
		return s;
	}
	
	static void addProperties(String s, Bioentity entity) {
		s = StringUtils.trimToNull(s);
		if (s != null) {
			String[] pairs = StringUtils.split(s, '|');
			for (String pairString : pairs) {
				String[] pair = StringUtils.split(pairString, "=", 2);
				if (pair.length == 2) {
					entity.addProperty(pair[0], pair[1]);
				}
			}
		}
	}
	
	static void addProperties(String s, GeneAnnotation ga) {
		s = StringUtils.trimToNull(s);
		if (s != null) {
			String[] pairs = StringUtils.split(s, '|');
			for (String pairString : pairs) {
				String[] pair = StringUtils.split(pairString, "=", 2);
				if (pair.length == 2) {
					ga.addProperty(pair[0], pair[1]);
				}
			}
		}
	}
	
	static void addXrefs(String s, Bioentity entity) {
		s = StringUtils.trimToNull(s);
		if (s != null) {
			String[] refs = StringUtils.split(s, '|');
			for (String ref : refs) {
				ref = StringUtils.trimToNull(ref);
				if (ref != null) {
					entity.addDbXref(ref);
				}
			}
		}
	}
	
	static void addXrefs(String s, GeneAnnotation ga) {
		s = StringUtils.trimToNull(s);
		if (s != null) {
			String[] refs = StringUtils.split(s, '|');
			for (String ref : refs) {
				ref = StringUtils.trimToNull(ref);
				if (ref != null) {
					ga.addReferenceId(ref);
				}
			}
		}
	}
	
	static void addSynonyms(String s, Bioentity entity) {
		s = StringUtils.trimToNull(s);
		if (s != null) {
			String[] synonyms = StringUtils.split(s, '|');
			for (String syn : synonyms) {
				syn = StringUtils.trimToNull(syn);
				if (syn != null) {
					entity.addSynonym(syn);
				}
			}
		}
	}

	/**
	 * Parse the string into a collection of with strings
	 * 
	 * @param withInfoString
	 * @return collection, never null
	 */
	public static Collection<String> parseWithInfo(final String withInfoString){
		Collection<String> infos = Collections.emptySet();
		if(withInfoString.length()>0){
			infos = new ArrayList<String>();
			String tokens[] = withInfoString.split("[\\||,]");
			for(String token: tokens){
				infos.add(token);
			}
		}
		return infos;
	}

	/**
	 * Parse the string into a list of qualifier strings
	 * 
	 * @param qualifierString
	 * @return collection, never null
	 */
	private static List<String> parseCompositeQualifier(String qualifierString){
		List<String> qualifiers = Collections.emptyList();
		if(qualifierString.length()>0){
			qualifiers = new ArrayList<String>();
			String tokens[] = qualifierString.split("[\\||,]");
			for(String token: tokens){
				qualifiers.add(StringUtils.trim(token));
			}
		}
		return qualifiers;
	}
	
	private static enum WithColumnData {
		
		contributesTo("contributes_to", "(contributes[_ ]to)"),
		colocalizesWith("colocalizes_with", "colocali[zs]es[_ ]with"),
		integralTo("integral_to", "integral[_ ]to"),
		not("NOT", "not"),
		cut("CUT", "cut");
		
		final String directMatch;
		final Pattern relaxedPattern;
		
		
		WithColumnData(String directMatch, String relaxedPattern) {
			this.directMatch = directMatch;
			this.relaxedPattern = Pattern.compile(relaxedPattern, Pattern.CASE_INSENSITIVE);
		}
		
		boolean matches(String qualifier, AnnotationParserMessages reporter) {
			if (qualifier.equals(directMatch)) {
				return true;
			}
			Matcher matcher = relaxedPattern.matcher(qualifier);
			if (matcher.find()) {
				String group = matcher.group();
				reporter.fireParsingWarning("Repairing qualifier '"+directMatch+"' from: "+group);
				return true;
			}
			return false;
		}
	}
	
	public static void parseQualifiers(GeneAnnotation ga, String qualifierString, AnnotationParserMessages reporter) {
		List<String> qualifiers = parseCompositeQualifier(qualifierString);
		List<String> unusedQualifiers = new ArrayList<String>();
		for (String qualifier : qualifiers) {
			boolean used = false;
			if (WithColumnData.contributesTo.matches(qualifier, reporter)) {
				if (ga.isContributesTo()) {
					reporter.fireParsingWarning("Duplicate qualifier: "+qualifier);
				}
				ga.setIsContributesTo(true);
				used = true;
			}
			else if (WithColumnData.colocalizesWith.matches(qualifier, reporter)) {
				if (ga.isColocatesWith()) {
					reporter.fireParsingWarning("Duplicate qualifier: "+qualifier);
				}
				ga.setIsColocatesWith(true);
				used = true;
			}
			else if (WithColumnData.integralTo.matches(qualifier, reporter)) {
				if (ga.isIntegralTo()) {
					reporter.fireParsingWarning("Duplicate qualifier: "+qualifier);
				}
				ga.setIsIntegralTo(true);
				used = true;
			}
			else if (WithColumnData.not.matches(qualifier, reporter)) {
				if (ga.isNegated()) {
					reporter.fireParsingWarning("Duplicate qualifier: "+qualifier);
				}
				ga.setIsNegated(true);
				used = true;
			}
			else if (WithColumnData.cut.matches(qualifier, reporter)) {
				if (ga.isCut()) {
					reporter.fireParsingWarning("Duplicate qualifier: "+qualifier);
				}
				ga.setIsCut(true);
				used = true;
			}
			if (used == false) {
				unusedQualifiers.add(qualifier);
			}
		}
		for (String unused : unusedQualifiers) {
			reporter.fireParsingError("Unknown qualifier: "+unused);
		}
	}
	
	public static Pair<String, String> parseTaxonRelationshipPair(String source) {
		source = StringUtils.trimToNull(source);
		if (source != null) {
			int open = source.indexOf('(');
			if (open > 0) {
				int close = source .indexOf(')', open);
				if (close > 0) {
					String rel = StringUtils.trimToNull(source.substring(0, open));
					String tax = StringUtils.trimToNull(source.substring(open+1, close));
					if (tax != null && rel != null) {
						return Pair.of(tax, rel);
					}
				}
			}
			else {
				return Pair.<String, String>of(source, null);
			}
			
		}
		return null;
	}
	
	/**
	 * @param extensionExpressionString
	 * @return list, never null
	 */
	public static List<List<ExtensionExpression>> parseExtensionExpression(String extensionExpressionString){
		List<List<ExtensionExpression>> groupedExpressions = Collections.emptyList();
		if(extensionExpressionString != null && extensionExpressionString.length() > 0){
			// first split by '|' to get groups
			String[] groups = StringUtils.split(extensionExpressionString, '|');
			groupedExpressions = new ArrayList<List<ExtensionExpression>>(groups.length);
			for (int i = 0; i < groups.length; i++) {
				// split by ',' to get individual entries
				String[] expressionStrings = StringUtils.split(groups[i], ',');
				List<ExtensionExpression> expressions = new ArrayList<ExtensionExpression>(expressionStrings.length);
				for (int j = 0; j < expressionStrings.length; j++) {
					String token = StringUtils.trimToEmpty(expressionStrings[j]);
					int index = token.indexOf("(");
					if(index > 0){
						String relation = StringUtils.trim(token.substring(0, index));
						String cls = StringUtils.trim(token.substring(index+1, token.length()-1));
						expressions.add(new ExtensionExpression(relation, cls));
					}
				}
				if (expressions.isEmpty() == false) {
					groupedExpressions.add(expressions);
				}
			}
			if (groupedExpressions.isEmpty()) {
				groupedExpressions = Collections.emptyList();
			}
		}
		return groupedExpressions;
	}

	public static String buildExtensionExpression(List<List<ExtensionExpression>> groupedExpressions) {
		StringBuilder sb = new StringBuilder();
		if (groupedExpressions != null && !groupedExpressions.isEmpty()) {
			for (List<ExtensionExpression> group : groupedExpressions) {
				if (sb.length() > 0) {
					sb.append('|');
				}
				for (int i = 0; i < group.size(); i++) {
					ExtensionExpression expression = group.get(i);
					if (i > 0) {
						sb.append(',');
					}
					sb.append(expression.getRelation()).append('(').append(expression.getCls()).append(')');
				}
			}
		}
		return sb.toString();
	}
	
	public static String buildPropertyExpression(List<Pair<String, String>> properties) {
		if (properties != null) {
			StringBuilder sb = new StringBuilder();
			for (Pair<String, String> pair : properties) {
				if (sb.length() > 0) {
					sb.append('|');
				}
				sb.append(pair.getLeft()).append('=').append(pair.getRight());
			}
			return sb.toString();
		}
		return null;
	}
	
	public static String buildTaxonString(String bioEntityTaxon, Pair<String, String> actsOnTaxonRelPair) {
		StringBuilder sb = new StringBuilder();
		if (bioEntityTaxon != null) {
			sb.append("taxon:").append(removePrefix(bioEntityTaxon, ':'));
		}
		if (actsOnTaxonRelPair != null) {
			if (sb.length() > 0) {
				sb.append('|');
			}
			String taxId = "taxon:"+removePrefix(actsOnTaxonRelPair.getLeft(), ':');
			String rel = actsOnTaxonRelPair.getRight();
			sb.append(rel).append("(").append(taxId).append(")");
		}
		if (sb.length() > 0) {
			return sb.toString();
		}
		return null;
	}
	
	public static String buildTaxonString(Pair<String, String> taxonRelPair) {
		if (taxonRelPair != null) {
			String taxId = "taxon:"+removePrefix(taxonRelPair.getLeft(), ':');
			String rel = taxonRelPair.getRight();
			if (rel != null) {
				return rel+"("+taxId+")";
			}
			return taxId;
		}
		return null;
	}
	
	public static String buildWithString(Collection<String> withInfos) {
		return buildWithString(withInfos, null);
	}
	
	public static String buildWithString(Collection<String> withInfos, String defaultString) {
		if (withInfos != null && !withInfos.isEmpty()) {
			return StringUtils.join(withInfos, '|');
		}
		return defaultString;
	}
	
//	public static String buildQualifierString(List<String> qualifierList) {
//		if (qualifierList != null && !qualifierList.isEmpty()) {
//			return StringUtils.join(qualifierList, '|');
//		}
//		return null;
//	}
	
	public static String buildGafQualifierString(GeneAnnotation ann) {
		StringBuilder sb = new StringBuilder();
		if (ann.isNegated()) {
			sb.append("NOT");
		}
		if (ann.isContributesTo()) {
			if (sb.length() > 0) {
				sb.append('|');
			}
			sb.append("contributes_to");
		}
		if (ann.isColocatesWith()) {
			if (sb.length() > 0) {
				sb.append('|');
			}
			sb.append("colocalizes_with");
		}
		if (ann.isIntegralTo()) {
			if (sb.length() > 0) {
				sb.append('|');
			}
			sb.append("integral_to");
		}
		if (ann.isCut()) {
			if (sb.length() > 0) {
				sb.append('|');
			}
			sb.append("CUT");
		}
		return sb.toString();
	}
	
	public static String buildGpadQualifierString(GeneAnnotation ann) {
		LinkedHashSet<String> qualifiers = new LinkedHashSet<String>();
		if (ann.isNegated()) {
			qualifiers.add("NOT");
		}
		String rel = ann.getRelation();
		if (ann.getRelation() != null) {
			qualifiers.add(rel);
		}
		if (ann.isContributesTo()) {
			qualifiers.add("contributes_to");
		}
		if (ann.isColocatesWith()) {
			qualifiers.add("colocalizes_with");
		}
		if (ann.isIntegralTo()) {
			qualifiers.add("integral_to");
		}
		if (ann.isCut()) {
			qualifiers.add("CUT");
		}
		if (qualifiers.isEmpty()) {
			return null;	
		}
	return StringUtils.join(qualifiers, '|');
	}
	
	public static String buildReferenceIdsString(List<String> referenceIds) {
		if (referenceIds != null && !referenceIds.isEmpty()) {
			return StringUtils.join(referenceIds, '|');
		}
		return null;
	}
}
