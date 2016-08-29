import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class inference
{
	public static int bCount;
	public static void main(String[] args) 
	{
		String fileName = "C:/Users/ashwini/Downloads/Test Cases [Updated 2]/input_1.txt";
		/*String fileName = null;
		if(args.length > 0)
		{
			fileName = args[1];	
		}*/
		List<String> queries = new ArrayList<String>();
		List<String> clauses = new ArrayList<String>();
		List<String> facts = new ArrayList<String>();
		Map<Integer, String> premises = new HashMap<Integer, String>();
		Map<Integer, String> cquents = new HashMap<Integer, String>();
		Map<Integer, String> qMap = new HashMap<Integer, String>();

		FileInputStream inputfile = null;
		try 
		{
			inputfile = new FileInputStream(fileName);
			BufferedReader reader = new BufferedReader(new InputStreamReader(inputfile));
			String queryCount = null;
			queryCount = reader.readLine();	
			int qCount = Integer.parseInt(queryCount);
			int p = 0;
			String query = null;
			while(p < qCount)
			{
				query = reader.readLine();
				queries.add(query);
				qMap.put(p+1, query);
				p++;
			}

			String clauseCount = null;
			clauseCount = reader.readLine();
			int clCount = Integer.parseInt(clauseCount);
			int q = 0;
			String clause = null;
			while(q < clCount)
			{
				clause = reader.readLine();
				clauses.add(clause);
				q++;
			}
		reader.close();
		} 
		catch (FileNotFoundException e) 
		{
			e.printStackTrace();
		} 
		catch (IOException e) 
		{
			e.printStackTrace();
		}

		//splitting clauses read from file
		splitClauses(clauses, premises, cquents, facts);
		//call backward chaining for each of the queries
		List<Map<String, String>> list;
		try 
		{
			File file = new File("output.txt");
			if(!file.exists())
			{
				file.createNewFile();
			}
			FileWriter fileWriter = new FileWriter(file.getAbsoluteFile());
			BufferedWriter bufferWriter = new BufferedWriter(fileWriter);
			for(int k=0; k<queries.size(); k++)
			{
				list = bcAsk(queries.get(k), premises, cquents, facts);
				if(list.isEmpty())
				{
					//System.out.println("FALSE");
					bufferWriter.write("FALSE");
					bufferWriter.newLine();
				}
				else
				{
					//System.out.println("TRUE");
					bufferWriter.write("TRUE");
					bufferWriter.newLine();
				}
			}
			bufferWriter.close();
			fileWriter.close();
		}
		catch (IOException e) 
		{
			e.printStackTrace();
		}

	}

	public static List<Map<String, String>> bcAsk(String query, Map<Integer, String> premises, Map<Integer, String> cquents, List<String> facts) 
	{
		List<String> entailed = new ArrayList<String>();
		List<String> qList = new ArrayList<String>();
		List<Map<String, String>> list;
		Map<String, String> subMap = new HashMap<String, String>();
		qList.add(query);
		list = backwardChaining(qList, premises, cquents, facts, entailed, subMap);
		return list;
	}

	public static List<Map<String, String>> backwardChaining(List<String> qList, Map<Integer, String> premises, Map<Integer, String> cquents, List<String> facts, List<String> entailed, Map<String, String> subMap) 
	{
		bCount = bCount + 1;
		String query = qList.get(0);
		Map<Integer, String> terms = returnTerms(query);
		Map<Integer, String> constants = new HashMap<Integer, String>();
		Map<Integer, String> variables = new HashMap<Integer, String>();
		List<String> remConjuncts = new ArrayList<String>();
		String queryPred = returnPredicate(query);
		String pConjunct = null;
		Map<String, String> tempSubMap = new HashMap<String, String>();
		List<Map<String, String>> tempResList = new ArrayList<Map<String,String>>();
		List<Map<String, String>> finalResList = new ArrayList<Map<String,String>>();
		List<Map<String, String>> newTempResList = new ArrayList<Map<String,String>>();
		
		entailed.add(query);
		//if the query is found in KB
		for(int h=0; h<facts.size(); h++)
		{
			if(query.contentEquals(facts.get(h)))
			{
				finalResList.add(subMap);
			}
		}

		String cquent = null;
		String cPred = null;
		Integer cKey = null;
		int count = 0;
		Map<Integer, Map<String, String>> allCquents = new HashMap<Integer, Map<String, String>>();
		for (Map.Entry<Integer,String> cEntry : cquents.entrySet())
		{
			tempSubMap.clear();
			cquent = cEntry.getValue();
			cKey = cEntry.getKey();
			cPred = returnPredicate(cquent);
			Map<String,String> temp = new HashMap<String,String>();
			if(cPred.contentEquals(queryPred))
			{
				count = count + 1;
				String premise = premises.get(cKey);
				temp.put(premise, cquent);
				allCquents.put(count,temp);
			}
		}

		outerloop:
			for(int p=1; p<=allCquents.size();p++)
			{
				String stdQuery;
				Map<String, String> cMap = allCquents.get(p);
				String cq = null;
				if(!cMap.isEmpty())
				{
					Object firstKey = cMap.keySet().toArray()[0];
					cq = cMap.get(firstKey);
				}
				stdQuery = standardizeQuery(cq,bCount);
				Map<Integer, String> cqTerms = returnTerms(stdQuery);
				int cqCount = 0;
				for(int k=1; k<=cqTerms.size(); k++)
				{
					String cqTerm = cqTerms.get(k);
					char ch = cqTerm.trim().charAt(0);
					if(!Character.isLowerCase(ch))
					{
						cqCount = cqCount+1;
						constants.put(cqCount, cqTerm);
					}
					else
					{
						cqCount = cqCount+1;
						variables.put(cqCount, cqTerm);
					}
				}
				tempSubMap = unify(terms, cqTerms);
				if(tempSubMap.isEmpty())
				{
					continue outerloop;
				}
				tempSubMap = compose(tempSubMap, subMap);
				if(!tempSubMap.isEmpty())
				{
					String premise = getKeyByValue(cMap, cq);
					if(premise != null)
					{
						List<String> pConjuncts = new ArrayList<String>();
						List<String> pConjunctsAll = splitConjuncts(premise);
						StringBuilder pConjunctsTemp = new StringBuilder();
						String stdPart;
						for(int k=0; k<pConjunctsAll.size(); k++)
						{
							String tempString = pConjunctsAll.get(k);
							stdPart = standardizeQuery(tempString, bCount);
							pConjunctsTemp.append(stdPart).append("^");
						}
						String xConjuncts = pConjunctsTemp.length() > 0 ? pConjunctsTemp.substring(0, pConjunctsTemp.length() - 1): "";
						pConjuncts = splitConjuncts(xConjuncts);
						pConjuncts = substitute(tempSubMap, pConjuncts);
						//checking for infinite loops
						for(int q=0; q<entailed.size(); q++)
						{
							for(int k=0; k<pConjuncts.size(); k++)
							{
								pConjunct = pConjuncts.get(k);
							}
							if(entailed.get(q).contentEquals(pConjunct))
							{
								continue outerloop;
							}
						}

						if(!pConjuncts.isEmpty())
						{
							List<Map<String, String>> temp = new ArrayList<Map<String, String>>();
							temp = backwardChaining(pConjuncts, premises, cquents, facts, entailed, tempSubMap);
							if(!temp.isEmpty())
							{
								finalResList.addAll(temp);
							}
						}
					}
					else
					{
						finalResList.add(tempSubMap);
					}
				}
			}
		if(qList.size() > 1)
		{
			remConjuncts = qList.subList(1, qList.size());
		}
		if(!finalResList.isEmpty())
		{
			for(int x=0; x<finalResList.size(); x++)
			{
				Map<String, String> tempMap = new HashMap<String, String>();
				tempMap = finalResList.get(x);
				if(!remConjuncts.isEmpty())
				{
					tempResList = backwardChaining(remConjuncts, premises, cquents, facts, entailed, tempMap);
					if(!tempResList.isEmpty())
					{
						if(!newTempResList.containsAll(tempResList))
						{
							newTempResList.addAll(tempResList);
						}
					}
				}
				else
				{
					return finalResList;
				}
			}
			return newTempResList;
		}
		return finalResList;
	}

	public static Map<String, String> compose(Map<String, String> tempSubMap, Map<String, String> subMap) 
	{
		Map<String, String> newSubMap = new HashMap<String, String>();
		newSubMap.putAll(subMap);
		for(Map.Entry<String, String> sEntry : tempSubMap.entrySet())
		{
			String sKey = sEntry.getKey();
			String sValue = sEntry.getValue();
			if(subMap.containsKey(sKey))
			{
				if(!sValue.contentEquals(subMap.get(sKey)))
				{
					newSubMap.clear();
					return newSubMap;
				}
			}
			else
				newSubMap.put(sKey, sValue);
		}
		return newSubMap;
	}

	public static List<String> substitute(Map<String, String> subMap, List<String> pConjuncts) 
	{
		Map<Integer, String> pTerms = new HashMap<Integer, String>();
		List<String> subConjuncts = new ArrayList<String>();
		Map<String, String> rMap = new HashMap<String, String>();
		List<String> keys = new ArrayList<String>();
		for (Map.Entry<String,String> sEntry : subMap.entrySet())
		{
			String key = sEntry.getKey();
			keys.add(key);
		}

		for(int k=0; k<pConjuncts.size(); k++)
		{
			String pConjunct = pConjuncts.get(k);
			pTerms = returnTerms(pConjunct);
			loop:
				for (Map.Entry<Integer,String> tempEntry : pTerms.entrySet())
				{
					String elem = tempEntry.getValue();
					String toReplace = elem;

					if(subMap.containsKey(elem))
					{
							for(int i=0; i<keys.size(); i++)
							{
								String subKey = keys.get(i);
								String subValue = subMap.get(subKey);
								if(subKey.contentEquals(elem))
								{
									if(Character.isUpperCase(subValue.charAt(0)))
									{
										rMap.put(toReplace, subValue);
										continue loop;
									}
									else
									{
										elem = subValue;
										i = 0;
									}
								}	
							}
					rMap.put(toReplace, elem);
					}
					else
					{
						rMap.put(elem, elem);
					}
				}

			String pred = returnPredicate(pConjunct);
			String term = pConjunct.substring(pConjunct.indexOf("(")+1, pConjunct.indexOf(")"));
			String value;
			if(!term.contains(","))
			{
				//single term
				value = rMap.get(term);
				term = value;
				pConjunct = pred+"("+term+")";
			}

			else
			{
				List<String> fin = new ArrayList<String>();
				StringBuilder res = new StringBuilder();
				String[] spltTerm = term.split(",");
				for(int g=0; g<spltTerm.length; g++)
				{
					String temp = spltTerm[g].trim();
					value = rMap.get(temp);
					fin.add(value);
				}
				for(String t : fin)
				{
					res.append(t);
					res.append(",");
				}
				String strTerm = res.length() > 0 ? res.substring(0, res.length() - 1): "";
				pConjunct = pred+"("+strTerm+")";
			}
			subConjuncts.add(pConjunct);
		}	
		return subConjuncts;
	}

	public static Map<String, String> unify(Map<Integer, String> terms, Map<Integer, String> cqTerms) 
	{
		Map<String, String> subMap = new HashMap<String, String>();
		for (Map.Entry<Integer,String> tEntry : cqTerms.entrySet())
		{
			Integer key = tEntry.getKey();
			String cqterm = tEntry.getValue();
			String subs = terms.get(key);
			if(Character.isUpperCase(cqterm.charAt(0)))
			{
				Character ch = subs.charAt(0);
				if(Character.isUpperCase(ch))
				{
					if(cqterm.contentEquals(subs))
					{
						subMap.put(cqterm, subs);
					}
					else
					{
						subMap.clear();
						return subMap;
					}
				}
				else
				{
					if(subMap.containsKey(subs))
					{
						if(!subMap.get(subs).contentEquals(cqterm))
						{
							subMap.clear();
							return subMap;
						}
					}
					else
					{
						subMap.put(subs, cqterm);
					}
					
				}
			}
			if(Character.isLowerCase(cqterm.charAt(0)))
			{
				subMap.put(cqterm, subs);
			}
		}
		return subMap;
	}

	public static String standardizeQuery(String cq, int count) 
	{
		StringBuilder term = new StringBuilder();
		String stdQuery;
		String terms = cq.substring(cq.indexOf("(")+1, cq.indexOf(")"));
		if(!terms.contains(","))
		{
			if(Character.isUpperCase(terms.charAt(0)))
			{
				stdQuery = cq;
			}
			else
			{
				term.append(terms).append(count);
				String queryPred = returnPredicate(cq);
				stdQuery = queryPred+"("+term+")";
			}
		}
		else
		{
			StringBuilder newS = new StringBuilder();
			String[] splitTerm = terms.split(",");
			for(int k=0; k<splitTerm.length; k++)
			{
				if(Character.isUpperCase(splitTerm[k].charAt(0)))
				{
					newS.append(splitTerm[k]);
				}
				else
				{
					newS.append(splitTerm[k]).append(count);
				}
				newS.append(",");
			}
			String newTerm = newS.length() > 0 ? newS.substring(0, newS.length() - 1): "";
			String queryPred = returnPredicate(cq);
			stdQuery = queryPred+"("+newTerm+")";
		}
		return stdQuery;
	}

	public static void splitClauses(List<String> clauses, Map<Integer, String> premises, Map<Integer, String> cquents, List<String> facts) 
	{
		int pcount = 0;
		//check '=>'
		for(int p=0; p<clauses.size(); p++)
		{
			String clause = clauses.get(p);
			if(clause.contains("=>"))
			{
				String[] parts = clause.split("=>");
				String premise = parts[0].trim();
				String cquent = parts[1].trim();
				pcount = pcount+1;
				premises.put(pcount, premise);
				cquents.put(pcount, cquent);
			}
			else
			{
				//put into facts
				facts.add(clause);
				pcount = pcount+1;
				cquents.put(pcount,clause);
			}
		}
	}

	//return predicate
	public static String returnPredicate(String clause)
	{
		String predicate = clause.substring(0, clause.indexOf('(')).trim();
		return predicate;
	}

	//return terms of predicate
	public static Map<Integer, String> returnTerms(String clause)
	{
		Map<Integer, String> terms = new HashMap<Integer, String>();
		String term = clause.substring(clause.indexOf("(")+1, clause.indexOf(")"));
		int tCount = 0;
		if(term.contains(","))
		{
			String[] tParts = term.split(",");
			for(int z=0; z<tParts.length; z++)
			{
				tCount = tCount+1;
				terms.put(tCount, tParts[z].trim());
			}
		}
		else
		{
			tCount = tCount+1;
			terms.put(tCount, term);
		}
		return terms;
	}

	//splits conjuncts
	public static List<String> splitConjuncts(String clause)
	{
		List<String> cList = new ArrayList<String>();
		if(clause.contains("^"))
		{
			String[] clSplit = clause.split("\\^");
			for(int m=0; m<clSplit.length; m++)
			{
				cList.add(clSplit[m].trim());
			}
		}
		else
		{
			cList.add(clause);
		}
		return cList;
	}

	//get key of consequent based on value
	public static String getKeyByValue(Map<String,String> cMap, String cquent)
	{
		String key = null;
		for (Map.Entry<String,String> entry : cMap.entrySet()) 
		{
			if (entry.getValue().equals(cquent)) 
			{
				key = entry.getKey();
			}
		}
		return key;
	}
}
