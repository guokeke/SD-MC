package com.songstan.ltl_trans.jni;

import java.io.IOException;
public class test {

	/**
	 * @param args
	 * @throws IOException
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		String arg = "(a U b)&&(c U d)";
		NFGJni jni = new NFGJni(arg);

		}


}
