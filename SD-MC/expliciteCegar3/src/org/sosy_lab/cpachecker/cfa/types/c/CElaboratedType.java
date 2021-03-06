/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2012  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.cfa.types.c;

public final class CElaboratedType extends CType {

  private final ElaboratedType kind;
  private final String   name;

  public CElaboratedType(boolean pConst, final boolean pVolatile,
      final ElaboratedType pKind, final String pName) {
    super(pConst, pVolatile);
    kind = pKind;
    name = pName.intern();
  }

  public String getName() {
    return name;
  }

  public ElaboratedType getKind() {
    return kind;
  }

  @Override
  public String toASTString(String pDeclarator) {
    StringBuilder lASTString = new StringBuilder();

    if (isConst()) {
      lASTString.append("const ");
    }
    if (isVolatile()) {
      lASTString.append("volatile ");
    }

    lASTString.append(kind.toASTString());
    lASTString.append(name);
    lASTString.append(" ");
    lASTString.append(pDeclarator);

    return lASTString.toString();
  }

  public static enum ElaboratedType {
    ENUM,
    STRUCT,
    UNION;

    public String toASTString() {
      return name().toLowerCase() + " ";
    }
  }
}