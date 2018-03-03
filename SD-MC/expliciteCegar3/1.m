frame(z, x, a, fp_executionPath, file) and(
	FILE* fp_executionPath <== fopen("D:\\Eclipse-TPChecker\\expliciteCegar3\\executionPath.txt", "w") and skip;
	FILE * file <== freopen("D:\\Eclipse-TPChecker\\expliciteCegar3\\values.txt", "r", stdin) and skip;

	int x and skip;
	int z and skip;
	int a and skip;

	scanf("%d", &x) and skip;
	scanf("%d", &z) and skip;
	scanf("%d", &a) and skip;
	
	while(a<3)
	{
	  fputs("[a<3] ", fp_executionPath) and skip;
	  a:=a+1
	};
	fputs("[!(a<3)] ", fp_executionPath) and skip;
	if(a=3)then{
	  fputs("[a=3] ", fp_executionPath) and skip;
	  z:=5
	};
	
	fclose(fp_executionPath) and skip
)
