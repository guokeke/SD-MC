package org.xidian.cpachecker.dz;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;


public class test {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
	  Set<Integer> set=new HashSet<Integer>();
	  List<Integer> list=new ArrayList<Integer>();
	  set.add(4);
	  list.add(4);
	  System.out.println(set.equals(list));

	}
	 public static String appendSpace(String  para){
	    int length = para.length();
	    char[] value = new char[length << 1];
	    for (int i=0, j=0; i<length; ++i, j = i << 1) {
	        value[j] = para.charAt(i);
	        value[1 + j] = ' ';
	    }
	    return new String(value);
	}

}
