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


public class inferenceTry
{
	public static void main(String[] args) 
	{
		String fileName = "E:/study/USC/Sem1-AI/Assignment 3/input_5.txt";
		/*String fileName = null;
		if(args.length > 0)
		{
			fileName = args[1];	
		}*/
		List<String> queries = new ArrayList<String>();
		List<String> clauses = new ArrayList<String>();
		List<String> facts = new ArrayList<String>();
		List<String> rules = new ArrayList<String>();
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
		for(int k=0; k<queries.size(); k++)
		{
			bcAsk(queries.get(k), premises, cquents, facts);
		}
	}

	public static void bcAsk(String query, Map<Integer, String> premises, Map<Integer, String> cquents, List<String> facts) 
	{
		Map<Integer, String> initTerms = new HashMap<Integer, String>();
		Map<String, String> resMap = new HashMap<String, String>();
		List<String> entailed = new ArrayList<String>();
		initTerms = returnTerms(query);
		String setValidity = null;
		List<String> list = new ArrayList<String>();
		list = backwardChaining(query, initTerms, premises, cquents, facts, entailed);
		if(!list.isEmpty())
		{
			System.out.println("TRUE");
			//writeToFile("TRUE");
		}
		else
		{
			System.out.println("FALSE");	
			//writeToFile("FALSE");
		}
	}

	public static List<String> backwardChaining(String query, Map<Integer, String> initTerms, Map<Integer, String> premises, Map<Integer, String> cquents, List<String> facts, List<String> entailed) 
	{
		Map<Integer, String> terms = returnTerms(query);
		Map<String, String> rMap = new HashMap<String, String>();
		Map<Integer, String> constants = new HashMap<Integer, String>();
		Map<Integer, String> variables = new HashMap<Integer, String>();
		List<String> remConjuncts = new ArrayList<String>();
		String queryPred = returnPredicate(query);
		String pConjunct = null;
		List<String> resList = new ArrayList<String>();
		List<String> tempResList = new ArrayList<String>();
		int rCount = 0;

		entailed.add(query);

		//if the query is found in KB
		for(int h=0; h<facts.size(); h++)
		{
			if(query.contentEquals(facts.get(h)))
			{
				//return list of substitution
				resList.add(query);
				return resList;
			}
		}

		String cquent = null;
		String cPred = null;
		Integer cKey = null;
		int count = 0;
		Map<Integer, Map<String, String>> allCquents = new HashMap<Integer, Map<String, String>>();
		for (Map.Entry<Integer,String> cEntry : cquents.entrySet())
		{
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
				Map<String, String> cMap = allCquents.get(p);
				String cq = null;
				if(!cMap.isEmpty())
				{
					Object firstKey = cMap.keySet().toArray()[0];
					cq = cMap.get(firstKey);
				}

				Map<Integer, String> cqTerms = returnTerms(cq);
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

				Map<String, String> cqSub = substitution(cq, initTerms, terms, variables, constants);
				if(cqSub.isEmpty())
				{
					continue outerloop;
				}
				String premise = getKeyByValue(cMap, cq);

				if(premise != null)
				{
					List<String> pConjuncts = splitConjuncts(premise);
					if(pConjuncts.size() > 1)
					{
						remConjuncts = pConjuncts.subList(1, pConjuncts.size());
					}
					pConjunct = pConjuncts.get(0);
					initTerms = returnTerms(pConjunct);
					pConjunct = unify(cqSub, pConjunct);

					//checking for infinite loops
					for(int q=0; q<entailed.size(); q++)
					{
						String entailedPred = returnPredicate(entailed.get(q));
						String checkPred = returnPredicate(pConjunct);
						if(entailed.get(q).contentEquals(pConjunct))
						{
							continue outerloop;
						}
					}
					resList = backwardChaining(pConjunct, initTerms, premises, cquents, facts, entailed);

					//check if returned list contains elements and keep track of substitution
					if(!resList.isEmpty())
					{	
						for(int r=0; r<remConjuncts.size(); r++)
						{
							List<String> tempList = new ArrayList<String>();
							String rConjunct = remConjuncts.get(r);
							Map<Integer, String> rInitTerms = returnTerms(rConjunct);
							Map<String, String> sMap = new HashMap<String, String>();
							innerloop:
								for(int q=0; q<resList.size(); q++)
								{
									String resElem = resList.get(q);
									Map<Integer, String> resTerms = returnTerms(resElem);
									for (Map.Entry<Integer,String> tEntry : initTerms.entrySet())
									{
										Integer initKey = tEntry.getKey();
										String initValue = tEntry.getValue();
										String cons = resTerms.get(initKey);
										sMap.put(initValue, cons);
									}
									//call backward chaining on the remaining conjuncts
									String newrConjunct = unify(sMap, rConjunct);
									tempResList = backwardChaining(newrConjunct, rInitTerms, premises, cquents, facts, entailed);
									if(tempResList.isEmpty())
									{
										tempList.add(resElem);
										continue innerloop;
									}
								}
							if(tempResList.isEmpty())
							{
								remConjuncts.clear();
								resList.clear();
							}
							resList.removeAll(tempList);
						}
					}
					//check if more elements are in all consequents list and then return
					else
					{
						continue outerloop;
					}
					return resList;
				}
				else
				{
					if(!resList.contains(cq))
					{
						resList.add(cq);
					}
				}
			}
		return resList;
	}

	public static Map<String,String> substitution(String cquent, Map<Integer, String> initTerms, Map<Integer, String> terms, Map<Integer, String> variables, Map<Integer, String> constants)
	{
		Map<String, String> subMap = new HashMap<String, String>();
		if(!variables.isEmpty())
		{
			for (Map.Entry<Integer,String> tEntry : terms.entrySet())
			{
				Integer elem = tEntry.getKey();
				String replaceWith = tEntry.getValue();
				String toReplace = variables.get(elem);
				if(toReplace != null)
				{
					String temp = toReplace.trim();
					toReplace = replaceWith;
					subMap.put(temp, toReplace);
				}
				else
				{
					continue;
				}
			}
		}
		if(!constants.isEmpty())
		{
			for (Map.Entry<Integer,String> tEntry : terms.entrySet())
			{
				Integer key = tEntry.getKey();
				String value = tEntry.getValue();
				char ch = value.charAt(0);
				if(Character.isUpperCase(ch))
				{
					if(value.equals(constants.get(key)))
					{
						subMap.put(initTerms.get(key), value);
					}
					else
					{
						subMap.clear();
						return subMap;
					}
				}
				else
				{
					//put x and constant ka value
					subMap.put(value, constants.get(key));
				}

			}
		}
		return subMap;
	}

	public static String unify(Map<String, String> subMap, String pConjunct) 
	{
		Map<Integer, String> conjunctTerms = returnTerms(pConjunct);
		Map<String, String> rMap = new HashMap<String, String>();
		for (Map.Entry<String,String> tempEntry : subMap.entrySet())
		{
			String elem = tempEntry.getValue();
			String elemKey = tempEntry.getKey();
			if(elemKey != null)
			{
				for(int h=1; h<=conjunctTerms.size(); h++)
				{
					String temp = conjunctTerms.get(h);
					if(temp.contentEquals(elemKey))
					{
						temp = elem;
						rMap.put(elemKey, temp);
					}
					else
					{
						if(!rMap.containsKey(temp))
						{
							rMap.put(temp, temp);
						}
					}
				}
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
		return pConjunct;
		//return conjunctTerms;
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

	//write to file
	public static void writeToFile(String output)
	{
		File file = new File("output.txt");
		try 
		{
			if(!file.exists())
			{
				file.createNewFile();
			}
			FileWriter fileWriter = new FileWriter(file.getName(),true);
			BufferedWriter bufferWriter = new BufferedWriter(fileWriter);
			if(!output.isEmpty())
			{
				bufferWriter.write(output);
				bufferWriter.newLine();
			}
			bufferWriter.close();
			fileWriter.close();	
		}
		catch (IOException e)
		{
			e.printStackTrace();
		}
	}
}
