/* 当前文件是D:\Read\main.c*/

#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#define FOR_RELEASE
#if ! defined FOR_RELEASE
#endif
int strncasecmp(const char *s1, const char *s2, size_t);
void mark_allocation_point(void);
void reset_allocation_point(void);
void initialize_memory(void);
#define TRUE  1
#define FALSE 0
#define OBS
#define assert(ex,string) {                                               \
if (!(ex)) {							  \
	printf("Assertion failed: %s\n", string); 		          \
	exit(1);							  \
}									  \
}
#define NEGATIVECOST -1000000
#define NOCUTOFF 1000
#ifndef MIN
#define MIN(X,Y)  ( ((X) < (Y)) ? (X) : (Y))
#endif
#ifndef MAX
#define MAX(X,Y)  ( ((X) > (Y)) ? (X) : (Y))
#endif
#define LEFT_WALL_DISPLAY  ("/////")
#define LEFT_WALL_SUPPRESS ("xxxxxxx")
				
#define RIGHT_WALL_DISPLAY  ("/////")
#define RIGHT_WALL_SUPPRESS ("RW")
#define LEFT_WALL_WORD   ("LEFT-WALL")
#define RIGHT_WALL_WORD  ("RIGHT-WALL")
#define POSTPROCESS_WORD ("POSTPROCESS")
#define ANDABLE_CONNECTORS_WORD ("ANDABLE-CONNECTORS")
#define PROPER_WORD      ("CAPITALIZED-WORDS")
#define HYPHENATED_WORD  ("HYPHENATED-WORDS")
#define NUMBER_WORD      ("NUMBERS")
#define UNKNOWN_WORD     ("UNKNOWN-WORD")
#define MAX_WORD 60
#define MAX_LINE 1500
#define MAX_SENTENCE 250
#define MAX_LINKS (2*MAX_SENTENCE-3)
#define MAX_TOKEN_LENGTH 50
#define PLURALIZATION
#define INFIX_NOTATION
#define DOWN_priority 2
#define UP_priority   1
#define THIN_priority 0
#define NORMAL_LABEL  (-1)

typedef struct Connector_struct Connector;
struct Connector_struct{
short label;
short word;
char priority;
char multi;
Connector * next;
char * string;
};
typedef struct Disjunct_struct Disjunct;
struct Disjunct_struct {
Disjunct *next;
short cost;
char marked;
char * string;
Connector *left, *right;
};
typedef struct Link_struct Link;
struct Link_struct {
int l, r;
Connector * lc, * rc;
char * name;
};
typedef struct Match_node_struct Match_node;
struct Match_node_struct {
Match_node * next;
Disjunct * d;
};
typedef struct Exp_struct Exp;
typedef struct X_node_struct X_node;
struct X_node_struct {
char * string;
Exp * exp;
X_node *next;
};
typedef struct Word_struct Word;
struct Word_struct {
char string[MAX_WORD];
X_node * x;
Disjunct * d;
};
typedef struct E_list_struct E_list;
struct Exp_struct {
char type;
unsigned char cost;
char dir;
char multi;
union {
	E_list * l;
	char * string;
}u;
};
struct E_list_struct {
E_list * next;
Exp * e;
};
#define OR_type 0
#define AND_type 1
#define CONNECTOR_type 2
typedef struct Word_file_struct Word_file;
struct Word_file_struct {
char file[MAX_WORD];
int changed;
Word_file * next;
};
typedef struct Dict_node_struct Dict_node;
struct Dict_node_struct {
char * string;
Word_file * file;
Exp * exp;
Dict_node *left, *right;
};
typedef struct Violation_list_struct Violation_list;
struct Violation_list_struct {
Violation_list * next;
char * string;
};
typedef struct D_type_list_struct D_type_list;
struct D_type_list_struct {
D_type_list * next;
int type;
};
typedef struct PP_node_struct PP_node;
struct PP_node_struct {
D_type_list ** d_type_array;
Violation_list * v;
};
typedef struct Linkage_info_struct Linkage_info;
struct Linkage_info_struct {
int index;
short N_violations, null_cost, disjunct_cost, and_cost, link_cost;
};
typedef struct List_o_links_struct List_o_links;
struct List_o_links_struct{
int link;
int word;
int dir;
List_o_links * next;
};

#define RTSIZE 256


#define GENTLE 1
#define RUTHLESS 0
Link link_array[MAX_LINKS];
int N_links;
char forgiving;
Disjunct * chosen_disjuncts[MAX_SENTENCE];
static int center[MAX_SENTENCE];
char * chosen_words[MAX_SENTENCE];
static int N_words_to_print;
unsigned int randtable[RTSIZE];
/* 当前文件是D:\Read\xalloc.c*/
#if 1
typedef unsigned int SIZET;
typedef struct {
SIZET size;
} Nuggie;
#define size_lval(x)    (((Nuggie *)(((char *)x) - sizeof(Nuggie)))->size)
#define prev_block(x)   (((char *) x) - (size_lval(x) & (~1)))
#define in_use(x)       (size_lval(x) & (1))
#define set_use(x)      (size_lval(x) |= (1))
#define clear_use(x)    (size_lval(x) &= (~1))
#define toggle_use(x)   (size_lval(x) ^= (1))
SIZET largest_block;
int max_space_in_use;
int space_in_use;
char * end_of_array;
char * start_of_array;
char * last_block;
#define MEMORY_LIMIT  ((30*1024*1024 * sizeof(char *))/4)
		
typedef double Align;
#define MEMORY_ALIGNMENT sizeof(Align)
#define ALIGNMENT_MASK (~(MEMORY_ALIGNMENT-1))
void initialize_memory(void) {
SIZET i, j;
if ((MEMORY_ALIGNMENT & (MEMORY_ALIGNMENT-1)) != 0) {
	fprintf(stderr, "sizeof(Align) is not a power of 2.\n");
	exit(1);	
}
for (i=0, j=1; i < j; i = j, j = (2*j+1)) largest_block = i;
largest_block &= ALIGNMENT_MASK;
largest_block += -sizeof(Nuggie);
start_of_array = (void *) malloc(MEMORY_LIMIT);
if (start_of_array == NULL) {
	fprintf(stderr, "Not enough memory for base pool.\n");
	exit(1);
}
end_of_array = start_of_array + ((sizeof(Nuggie) + MEMORY_ALIGNMENT-1) & ALIGNMENT_MASK);
size_lval(end_of_array) = 0;
max_space_in_use = 0;
space_in_use = 0;
last_block = NULL;
}
void * xalloc(int size) {
char * old_end_of_array;
if (((unsigned int) size) > largest_block) {
	fprintf(stderr, "Attempt to allocate too big a block (more than %d bytes)\n", largest_block);
	abort();
	exit(1);
}
old_end_of_array = end_of_array;
end_of_array += ((size+sizeof(Nuggie)) + MEMORY_ALIGNMENT-1) & ALIGNMENT_MASK;
size_lval(end_of_array) = end_of_array - old_end_of_array;
clear_use(end_of_array);
set_use(old_end_of_array);
last_block = old_end_of_array;
if (((unsigned int)(end_of_array-start_of_array)) > MEMORY_LIMIT) {
	fprintf(stderr, "Ran out of space.  Memory requested so far: %d bytes\n",
	       (end_of_array - start_of_array));
	exit(1);
}
space_in_use += size;
if (space_in_use > max_space_in_use) max_space_in_use = space_in_use;
return old_end_of_array;
}
void xfree(char * p, int size) {
char * q;
clear_use(p);
if (p == last_block) {
	while (1) {
	    q = prev_block(p);
	    if (q == p) {
		last_block = NULL;
		end_of_array = p;
		break;
	    }
	    if (in_use(q)) {
		last_block = q;
		end_of_array = p;
		break;
	    }
	    p = q;
	}
}
space_in_use -= size;
}
#endif
#if 0
int max_space_in_use;
int space_in_use;
#define MEMORY_LIMIT 32*1024*1024
#define MEMORY_ALIGNMENT 0x8
char    *memory_array;
int     memory_array_pointer = 0;
static int memory_array_marker=0;
void initialize_memory() {
memory_array = (char *) malloc(MEMORY_LIMIT);
if (memory_array==NULL) {
fprintf(stderr, "Not enough memory for base pool.\n");
exit(1);
}
}
void mark_allocation_point() {
memory_array_marker = memory_array_pointer;
}
void reset_allocation_point() {
memory_array_pointer = memory_array_marker;
}
void * xalloc(int size) {
int temp_pointer;
temp_pointer = memory_array_pointer & (~(MEMORY_ALIGNMENT-1));
if ((memory_array_pointer & (MEMORY_ALIGNMENT-1)) != 0) {
temp_pointer += MEMORY_ALIGNMENT;
}
memory_array_pointer = temp_pointer + size;
if (memory_array_pointer > MEMORY_LIMIT) {
fprintf(stderr, "Ran out of space.  Memory requested so far: %d bytes\n",
	   memory_array_pointer);
exit(1);
}
space_in_use += size;
if (space_in_use > max_space_in_use) max_space_in_use = space_in_use;
return (void *) (memory_array+temp_pointer);
}
void xfree(char * p, int size) {
if (p == NULL) return;
space_in_use -= size;
}
#endif
/* 当前文件是D:\Read\read-dict.c*/

int N_dict = 0;
Dict_node * dict_root = NULL;
static char token[MAX_TOKEN_LENGTH];
static int is_special;
int line_number = 1;
static FILE * dict_file;
void advance(void);
void error(char * s) {
int i;
printf("\nError in dictionary file: %s\n",s);
printf("line %d, tokens = ",line_number);
for (i=0; i<5 && token[0] != '\0' ; i++) {
	printf(" \"%s\"",token);
	(void) advance();
}
printf("\n");
exit(1);
}
void warning(char * s) {
printf("\nWarning: %s\n",s);
printf("line %d, current token = \"%s\"\n",line_number, token);
}
int get_character(int quote_mode) {
int c;
c = fgetc(dict_file);
if (c == '%' && !quote_mode) {
	while((c != EOF) && (c != '\n')) c = fgetc(dict_file);
}
if (c == '\n') line_number ++;
return c;
}
#define SPECIAL "(){};[]&|:"
void advance(void) {
int c, i;
static int already_got_it = '\0';
int quote_mode;
is_special = FALSE;
if (already_got_it != '\0') {
	is_special = (strchr(SPECIAL, already_got_it) != NULL);
	if (already_got_it == EOF) {
	    token[0] = '\0';
	} else {
	    token[0] = already_got_it;
	    token[1] = '\0';
	}
	already_got_it = '\0';
	return;
}
do c=get_character(FALSE); while (isspace(c));
quote_mode = FALSE;
i = 0;
for (;;) {
	if (i > MAX_TOKEN_LENGTH-1) {
	    error("Token too long");
	    return;
	}
	if (quote_mode) {
	    if (c == '\"') {
		quote_mode = FALSE;
		token[i] = '\0';
		return;
	    }
	    if (isspace(c)) {
		error("White space inside of token");
		return;
	    }	
	    token[i] = c;
	    i++;
	} else {
	    if (strchr(SPECIAL, c) != NULL) {
		if (i==0) {
		    token[0] = c;
		    token[1] = '\0';
		    is_special = TRUE;
		    return;
		}
		token[i] = '\0';
		already_got_it = c;
		return;
	    }
	    if (c==EOF) {
		if (i==0) {
		    token[0] = '\0';
		    return;
		}
		token[i] = '\0';
		already_got_it = c;
		return;
	    }
	    if (isspace(c)) {
		token[i] = '\0';
		return;
	    }
	    if (c == '\"') {
		quote_mode = TRUE;
	    } else {
		token[i] = c;
		i++;
	    }
	}
	c = get_character(quote_mode);
}
}
int is_equal(int c) {
return (is_special && c==token[0] && token[1] == '\0');
}
char * copy_string(char * str) {
char * s;
s = (char *) xalloc(strlen(str)+1);
strcpy(s, str);
return s;
}
void check_connector(char * s) {
int i;
i = strlen(s);
if (i < 1) {
	error("Expecting a connector.");
}
i = s[i-1];
if ((i!='+') && (i!='-')) {
	error("A connector must end in a \"+\" or \"-\".");
}
if (*s == '@') s++;
if (!isupper(*s)) {
	error("The first letter of a connector must be in [A--Z].");
}
if ((*s=='I') && (*(s+1)=='D')) {
	error("Connectors beginning with \"ID\" are forbidden");
}
while (*(s+1)) {
	if ((!isalnum(*s)) && (*s != '*') && (*s != '^')) {
	    error("All letters of a connector must be alpha-numeric.");
	}
	s++;
}
}
Exp * make_unary_node(Exp * e);
Exp * connector(void) {
Exp * n;
Dict_node * dn;
int i;
i = strlen(token)-1;
if ((token[i] != '+') && (token[i] != '-')) {
	dn = abridged_lookup(token);
	while((dn != NULL) && (strcmp(dn->string, token) != 0)) {
	    dn = dn->right;
	}
	if (dn == NULL) {
	    printf("\nPerhaps missing + or - in a connector.\n");
	    printf("Or perhaps you forgot the suffix on a word.\n");
	    error ("Or perhaps a word is used before it is defined\n");
	}
	n = make_unary_node(dn->exp);
} else {
	check_connector(token);
	n = (Exp *) xalloc(sizeof(Exp));
	n->dir = token[i];
	token[i] = '\0';
	if (token[0] == '@') {
	    n->u.string = copy_string(token+1);
	    n->multi = TRUE;
	} else {
	    n->u.string = copy_string(token);
	    n->multi = FALSE;
	}
	n->type = CONNECTOR_type;		
	n->cost = 0;
}
advance();
return n;
}
Exp * make_unary_node(Exp * e) {
Exp * n;
n = (Exp *) xalloc(sizeof(Exp));
n->type = AND_type;
n->cost = 0;
n->u.l = (E_list *) xalloc(sizeof(E_list));
n->u.l->next = NULL;
n->u.l->e = e;
return n;
}
Exp * make_zeroary_node(void) {
Exp * n;
n = (Exp *) xalloc(sizeof(Exp));
n->type = AND_type;
n->cost = 0;
n->u.l = NULL;
return n;
}
Exp * make_optional_node(Exp * e) {
Exp * n;
E_list *el, *elx;
n = (Exp *) xalloc(sizeof(Exp));
n->type = OR_type;
n->cost = 0;
n->u.l = el = (E_list *) xalloc(sizeof(E_list));
el->e = make_zeroary_node();
el->next = elx = (E_list *) xalloc(sizeof(E_list));
elx->next = NULL;
elx->e = e;
return n;
}
Exp * expression(void);
#if ! defined INFIX_NOTATION
Exp * operator_exp(int type) {
Exp * n;
E_list first;
E_list * elist;
n = (Exp *) xalloc(sizeof(Exp));
n->type = type;
n->cost = 0;
elist = &first;
while((!is_equal(')')) && (!is_equal(']')) && (!is_equal('}'))) {
	elist->next = (E_list *) xalloc(sizeof(E_list));
	elist = elist->next;
	elist->e = expression();
}
if (elist == &first) error("An \"or\" or \"and\" of nothing");
n->u.l = first.next;
return n;
}
Exp * in_parens(void) {
if (is_equal('&') || (strcmp(token, "and")==0)) {
	advance();
	return operator_exp(AND_type);
} else if (is_equal('|') || (strcmp(token, "or")==0)) {
	advance();
	return operator_exp(OR_type);
} else {
	return expression();
}
}
Exp * expression(void) {
Exp * n;
if (is_equal('(')) {
	advance();
	n = in_parens();
	if (!is_equal(')')) error("Expecting a \")\".");
	advance();
} else if (is_equal('{')) {
	advance();
	n = in_parens();
	if (!is_equal('}')) error("Expecting a \"}\".");
	advance();
	n = make_optional_node(n);
} else if (is_equal('[')) {
	advance();
	n = in_parens();
	if (!is_equal(']')) error("Expecting a \"]\".");
	advance();
	n->cost += 1;
} else if (!is_special) {
	n = connector();
} else if (is_equal(')') || is_equal(']')) {
n = make_zeroary_node();
} else {
	error("Connector, \"(\", \"[\", or \"{\" expected.");
}
return n;
}
#else
Exp * restricted_expression(int and_ok, int or_ok);
Exp * expression(void) {
return restricted_expression(TRUE,TRUE);
}
Exp * restricted_expression(int and_ok, int or_ok) {
Exp * nl=NULL, * nr, * n;
E_list *ell, *elr;
if (is_equal('(')) {
	advance();
	nl = expression();
	if (!is_equal(')')) error("Expecting a \")\".");
	advance();
} else if (is_equal('{')) {
	advance();
	nl = expression();
	if (!is_equal('}')) error("Expecting a \"}\".");
	advance();
	nl = make_optional_node(nl);
} else if (is_equal('[')) {
	advance();
	nl = expression();
	if (!is_equal(']')) error("Expecting a \"]\".");
	advance();
	nl->cost += 1;
} else if (!is_special) {
	nl = connector();
} else if (is_equal(')') || is_equal(']')) {
nl = make_zeroary_node();
} else {
	error("Connector, \"(\", \"[\", or \"{\" expected.");
}
if (is_equal('&') || (strcmp(token, "and")==0)) {
	if (!and_ok) {
	    warning("\"and\" and \"or\" at the same level in an expression");
	}
	advance();
	nr = restricted_expression(TRUE,FALSE);
	n = (Exp *) xalloc(sizeof(Exp));
	n->u.l = ell = (E_list *) xalloc(sizeof(E_list));
	ell->next = elr = (E_list *) xalloc(sizeof(E_list));
	elr->next = NULL;
	
	ell->e = nl;
	elr->e = nr;
	n->type = AND_type;
	n->cost = 0;
} else if (is_equal('|') || (strcmp(token, "or")==0)) {
	if (!or_ok) {
	    warning("\"and\" and \"or\" at the same level in an expression");
	}
	advance();
	nr = restricted_expression(FALSE,TRUE);
	n = (Exp *) xalloc(sizeof(Exp));
	n->u.l = ell = (E_list *) xalloc(sizeof(E_list));
	ell->next = elr = (E_list *) xalloc(sizeof(E_list));
	elr->next = NULL;
	ell->e = nl;
	elr->e = nr;
	n->type = OR_type;
	n->cost = 0;
} else return nl;
return n;
}
#endif
int dict_compare(char *s, char *t) {
while (*s != '\0' && *s == *t) {s++; t++;}
return (((*s == '.')?(1):((*s)<<1))  -  ((*t == '.')?(1):((*t)<<1)));
}
Dict_node * insert_dict(Dict_node * n, Dict_node * new) {
int comp;
if (n == NULL) return new;
comp = dict_compare(new->string, n->string);
if (comp < 0) {
n->left = insert_dict(n->left, new);
} else if (comp > 0) {
n->right = insert_dict(n->right, new);
} else {
printf("\"%s\"\n", new->string);
error("The word shown above has been multiply defined");
}
return n;
}
void insert_list(Dict_node * p, int l) {
Dict_node * dn, *dnx, *dn_second_half;
int k, i;
if (l == 0) return;
k = (l-1)/2;
dn = p;
for (i=0; i<k; i++) {
	dn = dn->left;
}
dn_second_half = dn->left;
dn->left = dn->right = NULL;
if (contains_underbar(dn->string)) {
	insert_idiom(dn);
} else if (is_idiom_word(dn->string)) {
printf("*** Word \"%s\" found near line %d.\n", dn->string, line_number);
printf("    Words ending \".Ix\" (x a number) are reserved for idioms.\n");
	printf("    This word will be ignored.\n");
} else if ((dnx = abridged_lookup(dn->string))!= NULL) {
	printf("*** The word \"%s\"", dn->string);
	printf(" found near line %d matches the following words:\n",
	       line_number);
	for (;dnx != NULL; dnx = dnx->right) {
	    printf(" %s", dnx->string);
	}
	printf("\n    This word will be ignored.\n");
} else {
	dict_root = insert_dict(dict_root, dn);
	N_dict++;
}
insert_list(p, k);
insert_list(dn_second_half, l-k-1);
}
void read_entry(void) {
Exp *n;
int i;
Dict_node  *dn_new, *dnx, *dn = NULL;
for (; !is_equal(':') ; advance()) {
	  if (is_special) {
	      error("I expected a word but didn\'t get it.");
	  }
	  if (token[0] == '/') {
	
	      dn = read_word_file(dn, token);
	  } else {
	      dn_new = (Dict_node *) xalloc(sizeof(Dict_node));
	      dn_new->left = dn;
	      dn = dn_new;
	      dn->file = NULL;
	      dn->string = copy_string(token);
	  }
}
advance();
n = expression();
if (!is_equal(';')) error("Expecting \";\" at the end of an entry.");
advance();
i = 0;
for (dnx = dn; dnx != NULL; dnx = dnx->left) {
	dnx->exp = n;
	i++;
}
insert_list(dn,i);
}
void print_expression(Exp * n) {
E_list * el; int i;
if (n == NULL) {
	printf("NULL expression");
	return;
}
if (n->type == CONNECTOR_type) {
	for (i=0; i<n->cost; i++) printf("[");
	printf("%s%c",n->u.string, n->dir);
	for (i=0; i<n->cost; i++) printf("] ");
} else {
	for (i=0; i<n->cost; i++) printf("[");
	if (n->cost == 0) printf("(");
	if (n->type == AND_type) printf("& ");
	if (n->type == OR_type) printf("or ");
	for (el = n->u.l; el != NULL; el = el->next) {
	    print_expression(el->e);
	}
	for (i=0; i<n->cost; i++) printf("] ");
	if (n->cost == 0) printf(") ");
}
}
void rprint_dictionary_data(Dict_node * n) {
	if (n==NULL) return;
	rprint_dictionary_data(n->left);
	printf("%s: ", n->string);
	print_expression(n->exp);
	printf("\n");
	rprint_dictionary_data(n->right);
}
void print_dictionary_data(void) {
rprint_dictionary_data(dict_root);
}
void read_dictionary(void) {
advance();
while(token[0] != '\0') {
	read_entry();
}
}
#if 0
OBS static int where_in_line;
OBS
OBS void rprint_dictionary_words(Dict_node * dn) {
OBS     if (dn == NULL) return;
OBS     rprint_dictionary_words(dn->left);
OBS     if (where_in_line+strlen(dn->string) > 70) {
OBS 	where_in_line = 0;
OBS 	printf("\n    ");
OBS     }
OBS     where_in_line += strlen(dn->string) + 1;
OBS     printf("%s ", dn->string);
OBS     rprint_dictionary_words(dn->right);
OBS }
OBS
OBS void print_dictionary_words(void) {
OBS     where_in_line = 1000;
OBS     rprint_dictionary_words(dict_root);
OBS     printf("\n\n");
OBS     printf("There are %d words in the dictionary.\n",N_dict);
OBS }
#endif
int dict_match(char * s, char * t) {
while((*s != '\0') && (*s == *t)) {s++; t++;}
if ((*s == '*') || (*t == '*')) return 0;
return (((*s == '.')?('\0'):(*s))  -  ((*t == '.')?('\0'):(*t)));
}
int true_dict_match(char * s, char * t) {
char *ds, *dt;
ds = strrchr(s, '.');
dt = strrchr(t, '.');
if ((dt != NULL) && ((*(dt+1) == '\0') || (isdigit(*(dt+1))))) dt = NULL;
if ((ds != NULL) && ((*(ds+1) == '\0') || (isdigit(*(ds+1))))) ds = NULL;
if (dt == NULL && ds != NULL) {
	if (((int)strlen(t)) > (ds-s)) return FALSE;
	return (strncmp(s, t, ds-s) == 0);
} else if (dt != NULL && ds == NULL) {
	if (((int)strlen(s)) > (dt-t)) return FALSE;
	return (strncmp(s, t, dt-t) == 0);
} else {
	return (strcmp(s, t) == 0);	
}
}
static Dict_node * lookup_list = NULL;
void prune_lookup_list(char * s) {
Dict_node *dn, *dnx, *dn_new;
dn_new = NULL;
for (dn = lookup_list; dn!=NULL; dn = dnx) {
	dnx = dn->right;
	
	if (true_dict_match(dn->string, s)) {
	    dn->right = dn_new;
	    dn_new = dn;
	} else {
	    xfree((char *)dn, sizeof(Dict_node));	
	}
}
lookup_list = NULL;
for (dn = dn_new; dn!=NULL; dn = dnx) {
	dnx = dn->right;
	dn->right = lookup_list;
	lookup_list = dn;
}
}
void free_lookup_list(void) {
Dict_node * n;
while(lookup_list != NULL) {
	n = lookup_list->right;
	xfree((char *)lookup_list, sizeof(Dict_node));
	lookup_list = n;
}
}
void rdictionary_lookup(Dict_node * dn, char * s) {
int m;
Dict_node * dn_new;
if (dn == NULL) return;
m = dict_match(s, dn->string);
if (m >= 0) {
rdictionary_lookup(dn->right, s);
}
if (m == 0) {
dn_new = (Dict_node*) xalloc(sizeof(Dict_node));
	*dn_new = *dn;
dn_new->right = lookup_list;
lookup_list = dn_new;
}
if (m <= 0) {
rdictionary_lookup(dn->left, s);
}
}
Dict_node * dictionary_lookup(char *s) {
free_lookup_list();
rdictionary_lookup(dict_root, s);
prune_lookup_list(s);
return lookup_list;
}
#if 0
OBS Dict_node * dictionary_lookup(char *s) {
OBS
OBS     int rboolean_dictionary_lookup(Dict_node * dn, char * s) {
OBS     int m;
OBS     if (dn == NULL) return FALSE;
OBS     m = dict_match(s, dn->string);
OBS     if (m < 0) {
OBS         return rboolean_dictionary_lookup(dn->left, s);
OBS     } else if (m == 0) {
OBS         return TRUE;
OBS     } else {
OBS         return rboolean_dictionary_lookup(dn->right, s);
OBS     }
OBS }
OBS
OBS int boolean_dictionary_lookup(char *s) {
OBS
OBS     return rboolean_dictionary_lookup(dict_root, s);
OBS }
#endif
int boolean_dictionary_lookup(char *s) {
return (dictionary_lookup(s) != NULL);
}
void rabridged_lookup(Dict_node * dn, char * s) {
int m;
Dict_node * dn_new;
if (dn == NULL) return;
m = dict_match(s, dn->string);
if (m >= 0) {
rabridged_lookup(dn->right, s);
}
if ((m == 0) && (!is_idiom_word(dn->string))) {
dn_new = (Dict_node*) xalloc(sizeof(Dict_node));
	*dn_new = *dn;
dn_new->right = lookup_list;
lookup_list = dn_new;
}
if (m <= 0) {
rabridged_lookup(dn->left, s);
}
}
Dict_node * abridged_lookup(char *s) {
free_lookup_list();
rabridged_lookup(dict_root, s);
prune_lookup_list(s);
return lookup_list;
}
int boolean_abridged_lookup(char *s) {
return (abridged_lookup(s) != NULL);
}
static Dict_node * parent;
static Dict_node * to_be_deleted;
int find_one_non_idiom_node(Dict_node * p, Dict_node * dn, char * s) {
int m;
if (dn == NULL) return FALSE;
m = dict_match(s, dn->string);
if (m <= 0) {
	if (find_one_non_idiom_node(dn,dn->left, s)) return TRUE;
}
if ((m == 0) && (!is_idiom_word(dn->string))) {
	to_be_deleted = dn;
	parent = p;
	return TRUE;
}
if (m >= 0) {
	if (find_one_non_idiom_node(dn,dn->right, s)) return TRUE;
}
return FALSE;
}
void set_parent_of_node(Dict_node *p, Dict_node * del, Dict_node * new) {
if (p == NULL) {
	dict_root = new;
} else {
	if (p->left == del) {
	    p->left = new;
	} else if (p->right == del) {
	    p->right = new;
	} else {
	    assert(FALSE, "Dictionary broken?");
	}
}
}
int delete_dictionary_words(char * s) {
Dict_node *pred, *pred_parent;
if (!find_one_non_idiom_node(NULL, dict_root, s)) return FALSE;
for(;;) {
	
	if (to_be_deleted->file != NULL) {
	    to_be_deleted->file->changed = TRUE;
	}
	if (to_be_deleted->left == NULL) {
	    set_parent_of_node(parent, to_be_deleted, to_be_deleted->right);
	    xfree((char *)to_be_deleted, sizeof(Dict_node));
	} else {
	    pred_parent = to_be_deleted;
	    pred = to_be_deleted->left;
	    while(pred->right != NULL) {
		pred_parent = pred;
		pred = pred->right;
	    }
	    to_be_deleted->string = pred->string;
	    to_be_deleted->file = pred->file;
	    to_be_deleted->exp = pred->exp;
	    set_parent_of_node(pred_parent, pred, pred->left);
	    xfree((char *)pred, sizeof(Dict_node));
	}
	if (!find_one_non_idiom_node(NULL, dict_root, s)) return TRUE;
}
}
void open_dictionary(char * s) {
if ((dict_file = fopen(s, "r")) == NULL) {
	printf("Cannot open file %s\n", s);
	exit(1);
}
}
/* 当前文件是D:\Read\header.h*/


void read_dictionary(void);
void print_dictionary_data(void);
void print_dictionary_words(void);
void print_expression(Exp *);
X_node * build_word_expressions(char *);
int maxcost_of_sentence(void);
void build_sentence_disjuncts(int cost_cutoff);
Disjunct * build_disjuncts_for_dict_node(Dict_node *);
void open_dictionary(char *);
int boolean_dictionary_lookup(char *);
int boolean_abridged_lookup(char *);
Dict_node * dictionary_lookup(char *);
Dict_node * abridged_lookup(char *);
int delete_dictionary_words(char *);
int table_lookup(int, int, Connector *, Connector *, int);
void print_disjunct_counts(void);
void print_links_graphically(FILE *fp);
void print_links(FILE *fp);
void extract_links(int index, int cost);
PP_node * post_process(void);
int match(Connector *, Connector *);
int count(int lw, int rw, Connector *le, Connector *re, int cost);
void * xalloc(int);
void xfree(char *, int);
void prune(void);
void power_prune(int);
int prune_match(Connector *, Connector *);
void free_disjuncts(Disjunct *);
void free_X_nodes(X_node *);
void free_connectors(Connector *);
void init_randtable(void);
void init_table(void);
void free_table(void);
Dict_node * read_word_file(Dict_node *, char *);
int files_need_saving(void);
void save_files(void);
Dict_node * insert_dict(Dict_node *, Dict_node *);
void error(char *);
void insert_idiom(Dict_node *);
int contains_underbar(char *);
void print_disjunct_list(Disjunct *);
int is_idiom_word(char *);
Disjunct* eliminate_duplicate_disjuncts(Disjunct * );
void print_sentence(FILE *fp, int w);
void print_all_word_disjuncts(void);
Disjunct * copy_disjunct(Disjunct * );
Connector * copy_connectors(Connector *);
void free_strings(void);
void free_this_string_later(char *, int);
void free_lookup_list(void);
void build_AND_tables(void);
Disjunct * build_AND_disjunct_list(char *);
void free_AND_tables(void);
Disjunct * catenate_disjuncts(Disjunct *, Disjunct *);
X_node * catenate_X_nodes(X_node *, X_node *);
Disjunct * build_COMMA_disjunct_list(void);
Disjunct * explode_disjunct_list(Disjunct *);
void print_AND_statistics(void);
void init_fast_matcher(void);
void free_fast_matcher(void);
Match_node * form_match_list(int, Connector *, int, Connector *, int);
void put_match_list(Match_node *);
int next_power_of_two_up(int);
void init_andable_hash_table(void);
int upper_case_match(char *, char *);
void print_a_link(FILE *fp, int link);
char * intersect_strings(char *, char *);
void construct_comma(void);
void construct_either(void);
void construct_neither(void);
void construct_notonlybut(void);
void construct_both(void);
Disjunct * glom_wall_connector(Disjunct *);
void build_conjunction_tables(void);
int sentence_contains(char *);
int parse(int mincost);
void free_Exp(Exp *);
void free_E_list(E_list *);
Exp * copy_Exp(Exp *);
void expression_prune(void);
int size_of_expression(Exp *);
void construct_wall_expressions(void);
void print_expression_sizes(void);
Linkage_info analyze_fat_linkage(int);
Linkage_info analyze_thin_linkage(int);
void free_PP_node(PP_node *);
void compute_chosen_words(void);
int is_canonical_linkage(void);
void compute_pp_link_array_connectors(void);
int set_has_fat_down(void);
void left_print_string(FILE* fp, char *, char *);
void conjunction_prune(void);
Word sentence[MAX_SENTENCE];
int N_words;
int left_wall_defined;
int right_wall_defined;
int postprocess_defined;
int andable_defined;
int unknown_word_defined;
int capitalized_word_defined;
int maxlinklength = MAX_SENTENCE;
int null_link_search = TRUE;
int use_unknown_word = TRUE;
int verbosity = 0;
int screen_width = 79;
int display_short = TRUE;
int display_on = TRUE;
int display_links = FALSE;
int display_bad = FALSE;
int display_fat = FALSE;
int display_multiple = TRUE;
int display_postscript = FALSE;
int display_word_subscripts = TRUE;
int display_link_subscripts = TRUE;
int display_walls = FALSE;
int echo_on = FALSE;
int www_mode = FALSE;
int just_one = FALSE;
int linkage_count_limit = 5000;
int word_count_limit = MAX_SENTENCE;
int null_links = TRUE;
char is_conjunction[MAX_SENTENCE];
char * deletable[MAX_SENTENCE];
int parse_cost;
int mark_cost;
int N_in_table;
int N_hash_lookups;
int work_in_hash_lookups;
double cumulative_time;
int issue_sentence_word(char * s) {
if (*s == '\0') return TRUE;
if (strlen(s) >= MAX_WORD) {
	printf("The word \"%s\" is too long.\n", s);
	printf("A word can have a maximum of %d characters.\n", MAX_WORD-1);
	return FALSE;
}
if (N_words == MAX_SENTENCE) {
	printf("The sentence has too many words.\n");
	return FALSE;
}
strcpy(sentence[N_words].string, s);
N_words++;
return TRUE;
}
char * strip_left[] = {"(", "$", NULL};
char * strip_right[] = {")", "%", ",", ".", ":", ";", "?", "!", "'", "'s", NULL};
#define MAX_STRIP 10
int separate_word(char * w, char *wend, int is_first_word) {
int i, len, n_stripped;
int stripped[MAX_STRIP];
char word[MAX_WORD+1];
for (;;) {
	for (i=0; strip_left[i] != NULL; i++) {
	    if (strncmp(w, strip_left[i], strlen(strip_left[i])) == 0) {
		if (!issue_sentence_word(strip_left[i])) return FALSE;
		w += strlen(strip_left[i]);
		break;
	    }
	}
	if (strip_left[i] == NULL) break;
}
for (n_stripped = 0; n_stripped < MAX_STRIP; n_stripped++) {
	strncpy(word, w, wend-w);
	word[wend-w] = '\0';
	if (wend == w) break;
	if (boolean_dictionary_lookup(word)) break;
	if (is_first_word && isupper(word[0])) {
	    word[0] = tolower(word[0]);
	    if (boolean_dictionary_lookup(word)) {
		word[0] = toupper(word[0]);
		break;
	    }
	    word[0] = toupper(word[0]);
	}
	for (i=0; strip_right[i] != NULL; i++) {
	    len = strlen(strip_right[i]);
	    if ((wend-w) < len) continue;
	    if (strncmp(wend-len, strip_right[i], len) == 0) {
		stripped[n_stripped] = i;
		wend -= len;
		break;
	    }
	}
	if (strip_right[i] == NULL) break;
}
if (n_stripped == MAX_STRIP) {
	printf("\"%s\" is followed by too many punctuation marks.\n", word);
	return FALSE;
}
if (!issue_sentence_word(word)) return FALSE;
for (i=n_stripped-1; i>=0; i--) {
	if (!issue_sentence_word(strip_right[stripped[i]])) return FALSE;
}
return TRUE;
}
int separate_sentence(char * s) {
char *t;
int is_first;
N_words = 0;
if (left_wall_defined) if (!issue_sentence_word(LEFT_WALL_WORD)) return FALSE;
is_first = TRUE;
for(;;) {
	while(isspace(*s) || (*s == '\"')) s++;
	if (*s == '\0') break;
	for (t=s; !((isspace(*t) || (*t == '\"')) || *t=='\0'); t++);
	if (!separate_word(s, t, is_first)) return FALSE;
	is_first = FALSE;
	s = t;
	if (*s == '\0') break;
}
if (right_wall_defined) if (!issue_sentence_word(RIGHT_WALL_WORD)) return FALSE;
return (N_words > left_wall_defined + right_wall_defined);
}
int isnumber(char * s) {
if (!isdigit(*s)) return FALSE;
for (; *s != '\0'; s++) {
	if ((!isdigit(*s)) && (*s != '.') && (*s != ',')) {
	    return FALSE;
	}
}
return TRUE;
}
int ishyphenated(char * s) {
int hyp, nonalpha;
hyp = nonalpha = 0;
if (*s == '-') return FALSE;
while (*s != '\0') {
	if (!isalpha(*s) && !isdigit(*s) && (*s!='.') && (*s!=',')
	    && (*s!='-')) return FALSE;
	if (*s == '-') hyp++;
	s++;
}
return ((*(s-1)!='-') && (hyp>0));
}
void free_sentence_disjuncts(void) {
int i;
for (i=0; i<N_words; i++) {
	free_disjuncts(sentence[i].d);
}
}
void free_sentence_expressions(void) {
int i;
for (i=0; i<N_words; i++) {
	free_X_nodes(sentence[i].x);
}
}
int special_string(int i, char * s) {
X_node * e;
if (boolean_dictionary_lookup(s)) {
	sentence[i].x = build_word_expressions(s);
	for (e = sentence[i].x; e != NULL; e = e->next) {
	    e->string = sentence[i].string;
	}
	return TRUE;
} else {
	printf("To process this sentence your dictionary ");
	printf("needs the word \"%s\".\n", s);
	return FALSE;
}
}
void handle_unknown_word(int i, char * s) {
char *t;
X_node *d;
char str[MAX_WORD+1];
sentence[i].x = build_word_expressions(UNKNOWN_WORD);
if (sentence[i].x == NULL) assert(FALSE, "UNKNOWN_WORD should have been there");
for (d = sentence[i].x; d != NULL; d = d->next) {
	t = strchr(d->string, '.');
	if (t != NULL) {
	    sprintf(str, "%.50s[?].%.5s", s, t+1);
	} else {
	    sprintf(str, "%.50s[?]", s);
	}
	t = (char *) xalloc(strlen(str)+1);
	free_this_string_later(t, strlen(str)+1);
	strcpy(t,str);
	d->string = t;
}
}
int build_sentence_expressions(void) {
int i;
int first_word;
char * s, *t;
X_node * e;
if (left_wall_defined) {
	first_word = 1;
} else {
	first_word = 0;
}
for (i=0; i<N_words; i++) {
	s = sentence[i].string;
	if (boolean_dictionary_lookup(s)) {
	    sentence[i].x = build_word_expressions(s);
	} else if (isupper(s[0]) && capitalized_word_defined) {
	    if (!special_string(i,PROPER_WORD)) return FALSE;
	} else if (isnumber(s)){
	    if (!special_string(i,NUMBER_WORD)) return FALSE;
	} else if (ishyphenated(s)) {
	
	    if (!special_string(i,HYPHENATED_WORD)) return FALSE;
	} else if (unknown_word_defined && use_unknown_word) {
	
	    handle_unknown_word(i, s);
	} else {
	
	    assert(FALSE, "I should have found that word.");
	}
}
s = sentence[first_word].string;
if (isupper(s[0])) {
	t = (char *) xalloc(strlen(s)+1);
	free_this_string_later(t, strlen(s)+1);
	strcpy(t,s);
	t[0] = tolower(t[0]);
	if (boolean_dictionary_lookup(t)) {
	    if (boolean_dictionary_lookup(s)) {
		e = build_word_expressions(t);
		sentence[first_word].x = catenate_X_nodes(sentence[first_word].x, e);
	    } else {
		s[0] = tolower(s[0]);
		e = build_word_expressions(s);
		free_X_nodes(sentence[first_word].x);
		sentence[first_word].x = e;
	    }
	}
}
return TRUE;
}
void print_statistics(void) {
printf("\n");
printf("%d parse cost\n", parse_cost);
printf("%d mark cost\n", mark_cost);
printf("%d in hash table\n", N_in_table);
printf("%d hash lookups\n", N_hash_lookups);
printf("%f cost per lookup\n",(float)work_in_hash_lookups/N_hash_lookups);
#ifndef SPEC_CPU2000
printf("%d maximum bytes ever in use\n", max_space_in_use);
printf("%d unreclaimed space\n", space_in_use);
#endif
}
void clean_up_string(char * s) {
char * x, * y;
y = x = s;
while(*x != '\0') {
	if (!isspace(*x)) {
	    *y = *x; x++; y++;
	} else {
	    x++;
	}
}
*y = '\0';
}
struct {char * s; int * p; int isboolean; char * str;} user_variable[] = {
{"verbosity",           &verbosity,                0, "Level of detail to give about the computation"},
{"width",               &screen_width,             0, "The width of your screen"},
{"limit",               &linkage_count_limit,      0, "The maximum number of linkages processed"},
{"graphics",            &display_on,               1, "Graphical link display"},
{"multiple",            &display_multiple,         1, "Expansion of fat (conjunctive) linkages"},
{"short",               &display_short,            1, "Reduced height display"},
{"postscript",          &display_postscript,       1, "Generating of postscript data"},
{"links",               &display_links,            1, "Showing of complete link data"},
{"bad",                 &display_bad,              1, "Showing of linkages failing postprocessing"},
{"fat",                 &display_fat,              1, "Showing of fat (conjunctive) linkages"},
{"lsubscripts",         &display_link_subscripts,  1, "Showing of complete link labels"},
{"wsubscripts",         &display_word_subscripts,  1, "Showing of word subscripts"},
{"walls",               &display_walls,            1, "Always show the walls"},
{"null",                &null_link_search,         1, "Null link search"},
{"unknown",             &use_unknown_word,         1, "Using of the \"unknown word\" definition"},
{"echo",                &echo_on,                  1, "Echoing of input sentence"},
{"www",                 &www_mode,                 1, "Suppression of prompt"},
{"justone",             &just_one,                 1, "Displaying of just one linkage"},
{"",                    NULL,                      0, ""}
};
struct {char * s; char * str;} user_command[] = {
{"quit",         "Exit the system"},
{"save",         "Save your changes to the dictionary"},
{"variables",    "List user-settable variables and their functions"},
{"help",         "List the commands and what they do"},
{NULL,           NULL}
};
int is_numerical_rhs(char *s) {
if (*s=='+' || *s == '-') s++;
do {
	if (!isdigit(*s)) return FALSE;
	s++;
} while (*s != '\0');
return TRUE;
}
void massage_variables(int j) {
int i;
for (i=0; user_variable[i].p != NULL; i++) {
	if (user_variable[i].isboolean) {
	    (*(user_variable[i].p)) = !!(*(user_variable[i].p));
	}
}
if (!display_on && (display_multiple || display_bad || display_fat)) {
	if (user_variable[j].p == &(display_on)) {
	    display_multiple = display_bad = display_fat = FALSE;
	} else {
	    display_on = TRUE;
	}
} else if (display_on && !(display_multiple || display_bad || display_fat)) {
	if (user_variable[j].p == &(display_on)) {
	    display_multiple = TRUE;
	} else {
	    display_on = FALSE;
	}
}
}
void special_command(char * line) {
char *x, *y, *s;
char myline[1000];
int i, count, j, k;
strncpy(myline, line, sizeof(myline));
myline[sizeof(myline)-1] = '\0';
clean_up_string(myline);
s = myline;
s++;
j = k = -1;
count = 0;
for (i=0; user_variable[i].p != NULL; i++) {
	if (user_variable[i].isboolean && strncasecmp(s, user_variable[i].s, strlen(s)) == 0) {
	    count++;
	    j = i;
	}
}
for (i=0; user_command[i].s != NULL; i++) {
	if (strncasecmp(s, user_command[i].s, strlen(s)) == 0) {
	    count++;
	    k = i;
	}
}
if (count > 1) {
	printf("Ambiguous command.  Type \"!help\" or \"!variables\"\n");
	return;
} else if (count == 1) {
	if (j >= 0) {
	    *(user_variable[j].p) = !(*(user_variable[j].p));
	    printf("%s turned %s.\n", user_variable[j].str, (*(user_variable[j].p))?"on":"off");
	    massage_variables(j);
	    return;
	} else {
	    strcpy(s, user_command[k].s);
	}
}
if (strcmp(s,"quit") == 0) {
	if (!files_need_saving()) {
	    exit(1);
	} else {
	    printf("You have changed some files and not saved them.\n");
	    printf("Either save your files with \"!save\" and then quit,\n");
	    printf("or get out without saving your files with control-C.\n");
	}
	return;
}
if (strncmp(s, "mark", 4) == 0) {
	printf("mark: %s", line+6);
	fflush(stdout);
	return;
}
if (strcmp(s,"save") == 0) {
	if (files_need_saving()) {
	    save_files();
	} else {
	    printf("No changes to be saved.\n");
	}
	return;
}
if (strcmp(s, "variables")==0) {
	printf(" Variable     Controls                                      Value\n");
	printf(" --------     --------                                      -----\n");
	for (i=0; user_variable[i].p != NULL; i++) {
	    printf(" ");
	    left_print_string(stdout, user_variable[i].s, "             ");
	    left_print_string(stdout, user_variable[i].str, "                                              ");
	    printf("%5d", *user_variable[i].p);
	    if (user_variable[i].isboolean) {
		if (*user_variable[i].p) printf(" (On)"); else printf(" (Off)");
	    }
	    printf("\n");
	}
	printf("\n");
	printf("Toggle a boolean variable as in \"!links\", set a variable as in \"!width=100\".\n");
	return;
}
if (strcmp(s, "help")==0) {
	printf("Special commands always begin with \"!\".  Command and variable names\n");
	printf("can be abbreviated.  Here is a list of the commands:\n\n");
	for (i=0; user_command[i].s != NULL; i++) {
	    printf(" !");
	    left_print_string(stdout, user_command[i].s, "                  ");
	    left_print_string(stdout, user_command[i].str, "                                                    ");
	    printf("\n");
	}
	printf("\n");
	printf(" !!<string>         Print all the dictionary words matching <string>.\n");
	printf("                    Also print the number of disjuncts of each.\n");
	printf("\n");
	printf(" !-<string>         Delete all the dictionary words matching <string>.\n");
	printf("\n");
	printf(" !<string>=<word>   This indicates that a new word (<string>) is to be\n");
	printf("                    added to the dictionary.  Its definition will be the\n");
	printf("                    same as that of <word>, and, if appropriate, it will\n");
	printf("                    be added to the word file of <word>.\n");
	printf("\n");
	printf(" !<var>             Toggle the specified boolean variable.\n");
	printf("\n");
	printf(" !<var>=<val>       Assign that value to that variable.\n");
	return;
}
if (s[0] == '!') {
	Dict_node * dn;
	Disjunct * d1, * d2;
	int len;
	if ((dn=dictionary_lookup(s+1)) == NULL) {
	    printf("    \"%s\" matches nothing in the dictionary.\n", s+1);
	    return;
	}
	printf("Matches:\n");
	for (;dn != NULL; dn = dn->right) {
	    len=0;
	    d1 = build_disjuncts_for_dict_node(dn);
	    for(d2 = d1 ; d2!=NULL; d2 = d2->next){
		len++;
	    }
	    free_disjuncts(d1);
	    printf("          ");
	    left_print_string(stdout, dn->string, "                  ");
	    printf(" %5d  ", len);
	    if (dn->file != NULL) {
		printf("<%s>", dn->file->file);
	    }
	    printf("\n");
	}
	return;
}
if (*s == '-') {
	
	Dict_node * dn, *dn1;
	int count;
	dn=abridged_lookup(s+1);
	count = 0;
	if (dn == NULL) {
	    printf("    \"%s\" matches nothing in the dictionary.\n", s+1);
	    return;
	}
	
for (dn1 = dn; dn1 != NULL; dn1 = dn1->right) {
	    if (dn1->file == NULL) count++;
	}
	if (count != 0) {
	    printf("Note: \"%s\" ", s+1);
	    printf("matches the following words in the main dictionary:\n");
	    for (dn1 = dn; dn1 != NULL; dn1 = dn1->right) {
		if (dn1->file == NULL) printf(" %s ", dn1->string);
	    }
	    printf("\n");
	}
	printf("Deleting:\n");
	for (dn1 = dn; dn1 != NULL; dn1 = dn1->right) {
	    printf(" %s ", dn1->string);
	}
	if (!delete_dictionary_words(s+1)) {
	    assert(FALSE, "Attempt to delete a word not in the dictonary.");
	}
	printf("\n");
	return;
}
for (x=s; (*x != '=') && (*x != '\0') ; x++)
;
if (*x == '=') {
	Dict_node * dn, * dn_new;
	*x = '\0';
	y = x+1;
	x = s;
	
	if (is_numerical_rhs(y)) {
	    for (i=0; user_variable[i].p != NULL; i++) {
		if (strcmp(x, user_variable[i].s) == 0) break;
	    }
	    if (user_variable[i].p == NULL) {
		printf("There is no user variable called \"%s\".\n", x);
	    } else {
		*(user_variable[i].p) = atoi(y);
		printf("%s set to %d\n", x, atoi(y));
		massage_variables(i);
	    }
	    return;
	}
	if (is_idiom_word(x) || is_idiom_word(y)) {
	    printf("    words ending \".Ix\" (x a number) ");
	    printf("are reserved for idioms\n");
	    return;
	}
	if ((dn=abridged_lookup(x)) != NULL) {
	    printf("    \"%s\" matches words already in the dictionary:\n",s);
	    for (;dn != NULL; dn = dn->right) {
		printf("%s ", dn->string);
	    }
	    printf("\n");
	    return;
	}
	if ((dn=abridged_lookup(y)) == NULL) {
	    printf("    \"%s\" is not in the dictionary.\n", y);
	    return;
	}
	if ((dn->right != NULL) || (strcmp(y,dn->string) != 0)) {
	    printf("    Please be more precise.  \"%s\" matches:\n", y);
	    for (;dn != NULL; dn = dn->right) {
		printf("%s ", dn->string);
	    }
	    printf("\n");
	    return;
	}
	if (dn->file == NULL) {
	    printf("    \"%s\" is in the dictionary but not in a file.\n",y);
	    printf("    This word will not be saved.\n");
	}
	dn_new = (Dict_node *) xalloc(sizeof(Dict_node));
	dn_new->string = (char *) xalloc(strlen(x)+1);
	strcpy(dn_new->string, x);
	dn_new->left = dn_new->right = NULL;
	dn_new->file = dn->file;
	dn_new->exp = dn->exp;
	dict_root = insert_dict(dict_root, dn_new);
	printf("    \"%s\" added to the dictionary.\n", x);
	N_dict++;
	if (dn->file != NULL) dn->file->changed = TRUE;
	return;
}
printf("Try \"!help\".\n");
}
int sentence_in_dictionary(void){
int w, ok_so_far;
char * s;
ok_so_far = TRUE;
for (w=0; w<N_words; w++) {
	s = sentence[w].string;
	if (!boolean_dictionary_lookup(s) &&
	    !(isupper(s[0]) && (capitalized_word_defined)) &&
	    !ishyphenated(s) &&
	    !isnumber(s)) {
	    if (ok_so_far) {
		printf("The following words are not in the dictionary:");
		ok_so_far = FALSE;
	    }
	    printf(" \"%s\"", sentence[w].string);
	}
}
if (!ok_so_far) printf("\n");
return ok_so_far;
}
int sentence_contains(char * s) {
int w;
for (w=0; w<N_words; w++) {
	if (strcmp(sentence[w].string, s) == 0) return TRUE;
}
return FALSE;
}
void set_is_conjunction(void) {
int w;
char * s;
for (w=0; w<N_words; w++) {
	s = sentence[w].string;
	is_conjunction[w] = ((strcmp(s, "and")==0) || (strcmp(s, "or" )==0) ||
			     (strcmp(s, "but")==0) || (strcmp(s, "nor")==0));
}
}
int sentence_contains_conjunction(void) {
int w;
for (w=0; w<N_words; w++) {
	if (is_conjunction[w]) return TRUE;
}
return FALSE;
}
int conj_in_range(int lw, int rw) {
for (;lw <= rw; lw++) {
	if (is_conjunction[lw]) return TRUE;
}
return FALSE;
}
void build_deletable(void) {
int i,j,k;
for (i=0; i<N_words; i++) {
	deletable[i] = (char *) xalloc(N_words+1);
	for (j=0; j<=MIN(i+maxlinklength, N_words); j++) {
	    if (null_links) {
		deletable[i][j] = TRUE;
	    } else if (j == i+1) {
		deletable[i][j] = TRUE;
	    } else if ((j>i+2)&&(is_conjunction[i+1] || is_conjunction[j-1] ||
(strcmp(",",sentence[i+1].string)==0 && conj_in_range(i+2,j-1)) ||
	                        (strcmp(",",sentence[j-1].string)==0 && conj_in_range(j,N_words-1)))){
		deletable[i][j] = TRUE;
	    } else if (j > i) {
		for (k=i+1; k<j; k++) {
		    if ((strcmp("either", sentence[k].string) == 0) ||
			(strcmp("neither", sentence[k].string) == 0) ||
			(strcmp("both", sentence[k].string) == 0) ||
			(strcmp("not", sentence[k].string) == 0)) continue;
		    if ((strcmp("only", sentence[k].string)==0) && (k > i+1) &&
(strcmp("not", sentence[k-1].string)==0)) continue;
		    break;
		}
		deletable[i][j] = (k==j);
	    } else {
		deletable[i][j] = FALSE;
	    }
	}
}
}
void free_deletable(void) {
int w;
for (w=0; w<N_words; w++) {
	xfree((char *)deletable[w],N_words+1);
}
}
void install_fat_connectors(void) {
int i;
for (i=0; i<N_words; i++) {
	if (is_conjunction[i]) {
	    sentence[i].d = catenate_disjuncts(sentence[i].d,
			       build_AND_disjunct_list(sentence[i].string));
	} else {
	    sentence[i].d = catenate_disjuncts(sentence[i].d,
			       explode_disjunct_list(sentence[i].d));
	    if (strcmp(sentence[i].string, ",") == 0) {
		sentence[i].d = catenate_disjuncts(sentence[i].d,
					       build_COMMA_disjunct_list());
	    }
	}
}
}
int compare_parse(Linkage_info * p1, Linkage_info * p2) {
if (p1->N_violations != p2->N_violations) {
	return (p1->N_violations - p2->N_violations);
} else if (p1->disjunct_cost != p2->disjunct_cost) {
	return (p1->disjunct_cost - p2->disjunct_cost);
} else if (p1->and_cost != p2->and_cost) {
	return (p1->and_cost - p2->and_cost);
} else {
	return (p1->link_cost - p2->link_cost);
}
}
#if ! defined FOR_RELEASE
static double when_last_called;
static double when_parse_started;
double current_useage_time(void) {
struct rusage u;
getrusage (RUSAGE_SELF, &u);
return (u.ru_utime.tv_sec + ((double) u.ru_utime.tv_usec) / 1000000.0);
}
void clear_time(void) {
when_last_called = when_parse_started = current_useage_time();
}
void print_time(char * s) {
double new_t;
new_t = current_useage_time();
if (verbosity > 1) {
	printf("++++");
	left_print_string(stdout, s, "                                           ");
	printf("%7.2f seconds\n", new_t - when_last_called);
}
when_last_called = new_t;
}
void print_total_time(void) {
double new_t;
new_t = current_useage_time();
cumulative_time += (new_t - when_parse_started) ;
if (verbosity > 0) {
	printf("++++");
	left_print_string(stdout, "Total","                                           ");
	printf("%7.2f seconds (%7.2f total)\n",
	       new_t - when_parse_started, cumulative_time);
}
when_parse_started = new_t;
}
#else
void clear_time(void) {}
void print_time(char * s) {
if (verbosity > 1) {
	printf("++++%s\n", s);
}
}
void print_total_time(void) {}
#endif
void first_prepare_to_parse(void) {
if (echo_on) print_sentence(stdout, 2);
if (verbosity > 2) {
	printf("Raw expression sizes:\n");
	print_expression_sizes();
}
expression_prune();
print_time("Done expression pruning");
}
void prepare_to_parse(int cost_cutoff) {
int i;
build_sentence_disjuncts(cost_cutoff);
if (verbosity > 2) {
	printf("After expanding expressions into disjuncts:") ;
	print_disjunct_counts();
}
print_time("Built disjuncts");
for (i=0; i<N_words; i++) {
	sentence[i].d = eliminate_duplicate_disjuncts(sentence[i].d);
}
print_time("Eliminated duplicate disjuncts");
if (verbosity > 2) {
	printf("\nAfter expression pruning and duplicate elimination:\n");
	print_disjunct_counts();
}
set_is_conjunction();
if (sentence_contains_conjunction()) {
	build_deletable();
	
	power_prune(GENTLE);
	if (verbosity > 2) {
	    printf("\nAfter Gentle power pruning:\n");
	    print_disjunct_counts();
	}
	print_time("Finished gentle power pruning");
	N_in_table = N_hash_lookups = work_in_hash_lookups = mark_cost = 0;
	conjunction_prune();
	if (verbosity > 2) {
	    printf("\nAfter conjunction pruning:\n");
	    print_disjunct_counts();
	    print_statistics();
	}
	free_deletable();
	print_time("Done conjunction pruning");
	build_conjunction_tables();
	install_fat_connectors();
	construct_either();
	construct_neither();
	construct_notonlybut();
	
	construct_both();
	construct_comma();
	if (verbosity > 2) {
	    printf("After conjunctions, disjuncts counts:\n");
	    print_disjunct_counts();
	}
	print_time("Constructed fat disjuncts");
	
	prune();
	print_time("Pruned fat disjuncts");
	
	for (i=0; i<N_words; i++) {
	    sentence[i].d = eliminate_duplicate_disjuncts(sentence[i].d);
	}
	if (verbosity > 2) {
	    printf("After pruning and duplicate elimination:\n");
	    print_disjunct_counts();
	}
	print_time("Eliminated duplicate disjuncts (again)");
	
	if (verbosity > 2) print_AND_statistics();
}
power_prune(RUTHLESS);
if (verbosity > 2) {
	printf("\nAfter power-pruning:\n");
	print_disjunct_counts();
}
print_time("Ruthlessly power pruned");
N_in_table = N_hash_lookups = work_in_hash_lookups = parse_cost = 0;
init_fast_matcher();
init_table();
print_time("Initialized fast matcher and hash table");
}
void unprepare_parse(void) {
free_sentence_disjuncts();
if (sentence_contains_conjunction()) free_AND_tables();
free_fast_matcher();
free_table();
}
void final_unprepare_parse(void) {
free_sentence_expressions();
free_strings();
free_lookup_list();
}
int compute_linkage_arrays(int index, int cost) {
extract_links(index, cost);
return (set_has_fat_down());
}
void summary_line(int N_canonical_linkages, int N_valid_linkages, char * stagen, int give_up) {
if (N_canonical_linkages == 0) {
	if (give_up) {
	    printf("Not accepted (no linkage exists) at %s", stagen);
	} else {
	    printf("No linkages at %s", stagen);
	}
} else if (N_canonical_linkages==1) {
	if  (N_valid_linkages == 0){
	    if (give_up) {
		printf("Not accepted (unique linkage with P.P. violation) at %s", stagen);
	    } else {
		printf("Unique linkage with P.P. violation at %s", stagen);
	    }
	} else {
	    printf("Accepted at %s", stagen);
	}
} else {
	if (N_valid_linkages == 0) {
	    if (give_up) {
		printf("Not accepted (%d linkages, all with P.P. violations) at %s",   N_canonical_linkages, stagen);
	    }
	    else {
		printf("%d linkages (all with P.P. violations) at %s", N_canonical_linkages, stagen);
	    }
	} else {
	    printf("Accepted (%d linkages, %d with no P.P. violations) at %s", N_canonical_linkages, N_valid_linkages, stagen);
	}
}
if (display_bad) {
	printf(" (shown above)\n\n");
} else {
	printf("\n");
}
}
char * stage_name(int phase, int cost_cutoff, int null_count) {
static char answer[100];
int stage;
if (phase == 0) {
	if (cost_cutoff <= 1) stage = 1; else stage = 2;
	sprintf(answer, "stage %d", stage);
} else {
	sprintf(answer, "null count %d", null_count);
}
return answer;
}
void loop(void) {
int i, N_to_display, index;
int N_linkages;
int N_canonical_linkages;
int N_valid_linkages;
int has_fatlinks;
Linkage_info * linkage=NULL;
char line[MAX_LINE], message[80];
int line_set = FALSE;
int cost_cutoff, old_cost_cutoff, maxcost, success, give_up, phase, just_entered_phase_1, null_count;
char * stagen;
for(;;) {
	null_links = FALSE;
	
	free_lookup_list();
	free_strings();
	max_space_in_use = 0;
	space_in_use = 0;
	
	
	clear_time();
	
	
	
	if (!line_set) {
	    if (!www_mode) printf("> ");
	    if (www_mode) fflush(stdout);
	    if (fgets(line, MAX_LINE, stdin) == NULL) exit(1);
	}
	line_set = FALSE;
	if (line[strlen(line)-1] != '\n') {
	    printf("Your sentence is too long\n");
	    continue;
	}
	if (line[0] == '!') {
	    special_command(line);
	    continue;
	}
	if (!separate_sentence(line)) continue;
	if (N_words - left_wall_defined - right_wall_defined > word_count_limit) {
	    printf("Try a sentence with at most %d words.\n", word_count_limit);
	    continue;
	}
	if (!(unknown_word_defined && use_unknown_word)) {
	    if (!sentence_in_dictionary()) continue;
	}
	if (!build_sentence_expressions()) continue;
	maxcost = maxcost_of_sentence();
	
	print_time("Constructed disjunct expressions");
	
	first_prepare_to_parse();
	old_cost_cutoff = 1;
	prepare_to_parse(1);
	
	phase = 0;
	success = give_up = FALSE;
	cost_cutoff = 0;
	null_count = 0;
	while(!(success || give_up)) {
	
	    just_entered_phase_1 = FALSE;
	    if (phase == 0) {
		
	        if (cost_cutoff == 0) {
		    cost_cutoff = 1;
	        } else if (cost_cutoff == 1 && maxcost > 1) {
		    cost_cutoff = maxcost;
		} else {
		    phase = 1;
		    null_links = TRUE;
		    cost_cutoff = NOCUTOFF;
		    just_entered_phase_1 = TRUE;
		}
		if (cost_cutoff == maxcost && !null_link_search) give_up = TRUE;
		
	    } else {
		null_count++;
		give_up = (null_count >= N_words-1);
		
		
	    }
	
	    if (verbosity > 2 && phase == 0) printf("Cost cutoff: %d\n", cost_cutoff);
	
	    if (cost_cutoff != old_cost_cutoff) {
		unprepare_parse();
		prepare_to_parse(cost_cutoff);
		old_cost_cutoff = cost_cutoff;
	    }
	
	    if (just_entered_phase_1) {
		
		null_count = 1;
	    }
	    stagen = stage_name(phase, cost_cutoff, null_count);
	
	    if (phase == 0) {
		N_linkages = parse(0);
	    } else {
		N_linkages = parse(null_count);
	    }
	    if (N_linkages > linkage_count_limit) {
		printf("Warning: only the first %d of %d linkages will be considered.\n", linkage_count_limit, N_linkages);
		N_linkages = linkage_count_limit;
	    }
	
	    sprintf(message, "Counted %d linkges", N_linkages);
	    print_time(message);
	
	    N_canonical_linkages = N_valid_linkages = 0;
	
	    if (N_linkages != 0) {
		linkage = (Linkage_info *)xalloc(N_linkages * sizeof(Linkage_info));
		for (index=0; index < N_linkages; index++) {
		    has_fatlinks = compute_linkage_arrays(index, null_count);
		    if (has_fatlinks) {
			if (!is_canonical_linkage()) continue;
			linkage[N_canonical_linkages] = analyze_fat_linkage(FALSE);
		    } else {
			linkage[N_canonical_linkages] = analyze_thin_linkage(FALSE);
		    }
		    if (linkage[N_canonical_linkages].N_violations == 0) {
			N_valid_linkages++;
		    }
		    linkage[N_canonical_linkages].index = index;
		    N_canonical_linkages ++;
		}
		qsort((void *)linkage, N_canonical_linkages,
		      sizeof(Linkage_info),
		      (int (*)(const void *, const void *))compare_parse);
	    }
	
	    assert(! ((N_canonical_linkages == 0) && (N_linkages > 0) && (N_linkages < linkage_count_limit)),
		   "None of the linkages is canonical");
	
	    print_time("Postprocessed all linkages");
	
	    line_set = FALSE;
	    success = (N_valid_linkages > 0);
	
	    if (!display_bad) summary_line(N_canonical_linkages, N_valid_linkages, stagen, give_up);
	    if (display_bad) {
		N_to_display = N_canonical_linkages;
	    } else {
		N_to_display = N_valid_linkages;
	    }
	
	    if (display_on) {
		for (index=0; index < N_to_display; index++) {
		    has_fatlinks = compute_linkage_arrays(linkage[index].index, null_count);
		    compute_chosen_words();
		    if (N_canonical_linkages > 1) {
			printf("  Linkage %d", index+1);
		    } else {
			printf("  Unique linkage");
		    }
		    if (linkage[index].N_violations > 0) {
			printf(" (bad), ");
		    } else {
			printf(", ");
		    }
		    printf("cost vector = (%d, %d, %d)\n",
			   linkage[index].disjunct_cost,
			   linkage[index].and_cost,
			   linkage[index].link_cost);
		    if (has_fatlinks) {
			(void) analyze_fat_linkage(TRUE);
		    } else {
			(void) analyze_thin_linkage(TRUE);
		    }
		    if (index == N_to_display-1) break;
		    if (just_one) break;
		    if (www_mode) continue;
		    if (!display_bad) {
			
			printf("(press return for another)\n");
			printf("> ");
			if (fgets(line, MAX_LINE, stdin) == NULL) exit(1);
			for (i=0; line[i] != '\0'; i++) if (!isspace(line[i])) break;
			if (line[i] != '\0') {
			    line_set = TRUE;
			    break;
			}
		    }
		}
	    }
	    if (display_bad) summary_line(N_canonical_linkages, N_valid_linkages, stagen, give_up);
	    if (N_linkages != 0) {
		xfree((char *) linkage, N_linkages*sizeof(Linkage_info));
	    }
	}
	
	print_time("Displayed linkages");
	unprepare_parse();
	final_unprepare_parse();
	print_time("Freed all data structures");
	
	if (verbosity > 2) print_statistics();
	if (space_in_use != 0){
	    printf("Warning: %d bytes of space leaked.\n", space_in_use);
	}
	print_total_time();
}
}
void batch_process(void) {
int i;
int N_linkages;
int N_canonical_linkages;
int N_valid_linkages;
int index;
int has_fatlinks;
Linkage_info * linkage=NULL;
char s[MAX_LINE];
int errors;
int mc;
int cost_cutoff, old_cost_cutoff, maxcost, last_pass;
null_links = FALSE;
errors = 0;
for(;;) {
	free_lookup_list();
	free_strings();
	max_space_in_use = 0;
	space_in_use = 0;
	clear_time();
	
	if (fgets(s, MAX_LINE, stdin) == NULL) break;
	if (s[strlen(s)-1] != '\n') {
	    printf("Sentence too long\n");
	    continue;
	}
	for (i=0; isspace(s[i]); i++);
	if (s[i] == '%') continue;
	if (s[i] == '\0') continue;
	if ((s[i] == '*') || (s[i] == '+') || (s[i] == '#') || (s[i] == ':') || (s[i] == '-')) {
	    mc = s[i];
	    s[i] = ' ';
	} else {
	    mc = ' ';
	}
	
	if (s[0] == '!') {
	    special_command(s);
	    continue;
	}
	if (!separate_sentence(s)) continue;
	if (!(unknown_word_defined && use_unknown_word)) {
	    if (!sentence_in_dictionary()) {
		errors++;
		printf("--- in the following sentence:\n");
		printf("%c ", mc);
		print_sentence(stdout, 2);
		printf("\n");
		continue;
	    }
	}
	if (!build_sentence_expressions()) {
	    errors++;
	    continue;
	}
	maxcost = maxcost_of_sentence();
	print_time("Constructed disjunct expressions");
	if (echo_on) printf("%c ", mc);
	first_prepare_to_parse();
	last_pass = FALSE;
	cost_cutoff = 0;
	old_cost_cutoff = 1;
	prepare_to_parse(1);
	
	while (!last_pass) {
	    if (cost_cutoff == 0) {
		cost_cutoff = 1;
	    } else if (cost_cutoff == 1 && maxcost > 1) {
		cost_cutoff = maxcost;
	    }
	    last_pass = (cost_cutoff >= maxcost);
	
	    if (verbosity > 2) printf("Cost cutoff: %d  maxcost: %d\n", cost_cutoff, maxcost) ;
	
	    if (cost_cutoff != old_cost_cutoff) {
		unprepare_parse();
		prepare_to_parse(cost_cutoff);
		old_cost_cutoff = cost_cutoff;
	    }
	    N_linkages = parse(0);
	    print_time("Counted linkages");
	    N_canonical_linkages = N_valid_linkages = 0;
	    if (N_linkages != 0) {
		linkage = (Linkage_info *)xalloc(N_linkages*
						 sizeof(Linkage_info));
		for (index=0;(index < N_linkages) && (N_valid_linkages== 0);
		     index++) {
		
		    has_fatlinks = compute_linkage_arrays(index, 0);
		    if (has_fatlinks) {
			if (!is_canonical_linkage()) continue;
			linkage[N_canonical_linkages]=
			    analyze_fat_linkage(FALSE);
		    } else {
			linkage[N_canonical_linkages]=
			    analyze_thin_linkage(FALSE);
		    }
		    if (linkage[N_canonical_linkages].N_violations == 0) {
			N_valid_linkages++;
		    }
		    linkage[N_canonical_linkages].index = index;
		    N_canonical_linkages ++;
		}
		qsort((void *)linkage, N_canonical_linkages,
		      sizeof(Linkage_info),
		      (int (*)(const void *, const void *))compare_parse);
	    }
	    print_time("Postprocessed some linkages");
	
	    if (N_canonical_linkages == 0) {
	      if (!((mc == '*') || (mc == '#'))) {
		if (last_pass) {
		  errors++;
		  if (!echo_on) {
		    printf("--- No linkage for (%s): ", stage_name(0, cost_cutoff, 0));
		    if (echo_on) printf("%c ", mc);
		    print_sentence(stdout, 13);
		  } else {
		    printf("--- No linkage for this (%s)\n", stage_name(0, cost_cutoff, 0));
		  }
		} else {
		}
	      }
	    } else if (N_valid_linkages == 0) {
		if (!((mc == '+') || (mc == '*'))) {
		    if (last_pass) {
			if (N_canonical_linkages == 1) {
			    printf("--- unique linkage, with post-processing violation (%s)\n", stage_name(0, cost_cutoff, 0));
			} else {
			    printf("--- %d linkages", N_canonical_linkages);
			    printf(", all with post-processing violations");
			    printf(" (%s)\n",stage_name(0, cost_cutoff, 0));
			}
			errors++;
			has_fatlinks =
			    compute_linkage_arrays(linkage[0].index, 0);
			compute_chosen_words();
			if (has_fatlinks) {
			    (void) analyze_fat_linkage(TRUE);
			} else {
			    (void) analyze_thin_linkage(TRUE);
			}
		    } else {
		    }
		  }
	    } else if ((mc == '+') || (mc == '*') || (mc == '#')) {
		errors++;
		if (!echo_on) {
		  printf("--- %s Input: ", stage_name(0, cost_cutoff, 0));
		  printf("%c ", mc);
		  print_sentence(stdout, 13);
		} else {
		  printf("--- Accepted %s:\n", stage_name(0, cost_cutoff, 0));
		}
		last_pass = 1;
		has_fatlinks = compute_linkage_arrays(linkage[0].index, 0);
		compute_chosen_words();
		if (has_fatlinks) {
		    (void) analyze_fat_linkage(TRUE);
		} else {
		    (void) analyze_thin_linkage(TRUE);
		}
	    } else if ((linkage[0].disjunct_cost == 0) && (mc == ':')) {
		errors++;
		if (!echo_on) {
		  printf("--- %s Input:  ", stage_name(0, cost_cutoff, 0));
		  printf("%c ", mc);
		  print_sentence(stdout, 13);
		} else {
		  printf("--- Accepted %s:\n", stage_name(0, cost_cutoff, 0));
		}
		last_pass = 1;
		printf("p.p. violations: %d, disjunct cost: %d\n",
		       linkage[0].N_violations, linkage[0].disjunct_cost);
		has_fatlinks = compute_linkage_arrays(linkage[0].index, 0);
		compute_chosen_words();
		if (has_fatlinks) {
		    (void) analyze_fat_linkage(TRUE);
		} else {
		    (void) analyze_thin_linkage(TRUE);
		}
	    } else if ((cost_cutoff == 1) && (mc == '-')) {
	      errors++;
	      if (!echo_on) {
		printf("--- %s Input: ", stage_name(0, cost_cutoff, 0));
		printf("%c ", mc);
		print_sentence(stdout, 13);
	      } else {
		  printf("--- Accepted %s:\n", stage_name(0, cost_cutoff, 0));
		}
		last_pass = 1;
		has_fatlinks = compute_linkage_arrays(linkage[0].index, 0);
		compute_chosen_words();
		if (has_fatlinks) {
		    (void) analyze_fat_linkage(TRUE);
		} else {
		    (void) analyze_thin_linkage(TRUE);
		}
	    } else if (FALSE && (cost_cutoff > 1) && (mc == ' ')) {
		
		
		
		
	      errors++;
	      if (!echo_on) {
		  printf("--- %s Input: ", stage_name(0, cost_cutoff, 0));
		  printf("%c ", mc);
		  print_sentence(stdout, 13);
		} else {
		  printf("--- Accepted %s:\n", stage_name(0, cost_cutoff, 0));
		}
	      last_pass = 1;
	      has_fatlinks = compute_linkage_arrays(linkage[0].index, 0);
	      compute_chosen_words();
	      if (has_fatlinks) {
		  (void) analyze_fat_linkage(TRUE);
	      } else {
		  (void) analyze_thin_linkage(TRUE);
	      }
	
	    } else {
		last_pass = 1;
		
	    }
	    if (N_linkages != 0) {
		xfree((char *) linkage, N_linkages*sizeof(Linkage_info));
	    }
	}
	fflush(stdout);
	print_time("Displayed linkages");
	unprepare_parse();
	final_unprepare_parse();
	print_time("Freed all data structures");
	if (verbosity > 2) print_statistics();
	if (space_in_use != 0){
	    printf("Warning: %d bytes of space leaked.\n", space_in_use);
	}
	print_total_time();
}
if (errors == 0) {
	printf("No errors!\n");
} else if (errors == 1) {
	printf("One error.\n");
} else {
	printf("%d errors.\n", errors);
}
}
int temp_ver=0;
int main(int argc, char** argv) {
int batch;
int prob;
int i;
(void) initialize_memory();
prob = FALSE;
batch = FALSE;
for (i=2; i<argc && !prob; i++) {
	if (strcmp(argv[i], "-wordlimit") == 0) {
	    prob = (i == argc-1 || (sscanf(argv[i+1], "%d", &word_count_limit) != 1));
	    i++;
	} else if (strcmp(argv[i], "-linklimit") == 0) {
	    prob = (i == argc-1 || (sscanf(argv[i+1], "%d", &linkage_count_limit) != 1));
	    i++;
	} else if (strcmp(argv[i], "-batch") == 0) {
	    batch = TRUE;
	}
}	
if ((argc < 2) || prob) {
	fprintf(stderr, "Usage: %s dictionary-file [-batch] [-wordlimit number] [-linklimit number]\n", argv[0]);
	exit(1);
}
open_dictionary(argv[1]);
printf("\n Reading the dictionary files: ");
read_dictionary();
#ifndef SPEC_CPU2000
printf("\n %d words stored in %d bytes\n\n\n", N_dict, space_in_use);
#else
printf("\n\n\n");
#endif
printf("Welcome to the Link Parser -- Version 2.1\n\n");
printf("          ");
printf("Copyright (C) 1991-1995 Daniel Sleator and Davy Temperley\n\n");
init_randtable();
left_wall_defined = boolean_dictionary_lookup(LEFT_WALL_WORD);
right_wall_defined = boolean_dictionary_lookup(RIGHT_WALL_WORD);
postprocess_defined = boolean_dictionary_lookup(POSTPROCESS_WORD);
andable_defined = boolean_dictionary_lookup(ANDABLE_CONNECTORS_WORD);
unknown_word_defined = boolean_dictionary_lookup(UNKNOWN_WORD);
capitalized_word_defined = boolean_dictionary_lookup(PROPER_WORD);
if (andable_defined) {
	init_andable_hash_table();
}
if (batch) {
	printf("Processing sentences in batch mode\n");
	printf("\n");
	batch_process();
} else {
	printf("Type your sentence and press Return ");
	printf("(\"!help\" for options).\n");
	printf("\n");
	loop();
}
temp_ver=1;
return 0;
}
/* 当前文件是D:\Read\analyze-linkage.c*/

Link pp_link_array[MAX_LINKS];
typedef struct DIS_node_struct DIS_node;
typedef struct CON_node_struct CON_node;
typedef struct CON_list_struct CON_list;
typedef struct DIS_list_struct DIS_list;
typedef struct Links_to_patch_struct Links_to_patch;
typedef void (*void_returning_function)();
struct DIS_node_struct {
CON_list * cl;
List_o_links * lol;
int word;
};
struct CON_node_struct {
DIS_list * dl;
DIS_list * current;
int word;
};
struct DIS_list_struct {
DIS_list * next;
DIS_node * dn;
};
struct CON_list_struct {
CON_list * next;
CON_node * cn;
};
struct Links_to_patch_struct {
Links_to_patch * next;
int link;
char dir;
int new;
};
static List_o_links * word_links[MAX_SENTENCE];
void build_digraph(void) {
int i, link, N_fat;
Link * lp;
List_o_links * lol;
N_fat = 0;
for (i=0; i<N_words; i++) {
	word_links[i] = NULL;
}
for (link=0; link<N_links; link++) {
	lp = &link_array[link];
	i = lp->lc->label;
	if (i < NORMAL_LABEL) {
	    continue;
	}
	lol = (List_o_links *) xalloc(sizeof(List_o_links));
	lol->next = word_links[lp->l];
	word_links[lp->l] = lol;
	lol->link = link;
	lol->word = lp->r;
	i = lp->lc->priority;
	if (i == THIN_priority) {
	    lol->dir = 0;
	} else if (i == DOWN_priority) {
	    lol->dir = 1;
	} else {
	    lol->dir = -1;
	}
	lol = (List_o_links *) xalloc(sizeof(List_o_links));
	lol->next = word_links[lp->r];
	word_links[lp->r] = lol;
	lol->link = link;
	lol->word = lp->l;
	i = lp->rc->priority;
	if (i == THIN_priority) {
	    lol->dir = 0;
	} else if (i == DOWN_priority) {
	    lol->dir = 1;
	} else {
	    lol->dir = -1;
	}
}
}
static int structure_violation;
static int dfs_root_word[MAX_SENTENCE];
int is_CON_word(int w) {
List_o_links * lol;
for (lol = word_links[w]; lol!=NULL; lol = lol->next) {
	if (lol->dir == 1) {
	    return TRUE;
	}
}
return FALSE;
}
DIS_node * build_DIS_node(int);
CON_list * c_dfs(int, DIS_node *, CON_list *);
CON_node * build_CON_node(int w) {
List_o_links * lol;
CON_node * a;
DIS_list * d, *dx;
d = NULL;
for (lol = word_links[w]; lol!=NULL; lol = lol->next) {
	if (lol->dir == 1) {
	    dx = (DIS_list *) xalloc (sizeof (DIS_list));
	    dx->next = d;
	    d = dx;
	    d->dn = build_DIS_node(lol->word);
	}
}
a = (CON_node *) xalloc(sizeof (CON_node));
a->dl = a->current = d;
a->word = w;
return a;
}
CON_list * c_dfs(int w, DIS_node * start_dn, CON_list * c) {
CON_list *cx;
List_o_links * lol, *lolx;
if (dfs_root_word[w] != -1) {
	if (dfs_root_word[w] != start_dn->word) {
	    structure_violation = TRUE;
	}
	return c;
}
dfs_root_word[w] = start_dn->word;
for (lol=word_links[w]; lol != NULL; lol = lol->next) {
	if (lol->dir < 0) {
	    if (dfs_root_word[lol->word] == -1) {
		structure_violation = TRUE;
	    }
	} else if (lol->dir == 0) {
	    lolx = (List_o_links *) xalloc(sizeof(List_o_links));
	    lolx->next = start_dn->lol;
	    lolx->link = lol->link;
	    start_dn->lol = lolx;
	    c = c_dfs(lol->word, start_dn, c);
	}
}
if (is_CON_word(w)) {
	cx = (CON_list *) xalloc(sizeof(CON_list));
	cx->next = c;
	c = cx;
	c->cn = build_CON_node(w);
}
return c;
}
DIS_node * build_DIS_node(int w) {
DIS_node * dn;
dn = (DIS_node *) xalloc(sizeof (DIS_node));
dn->word = w;
dn->lol = NULL;
dn->cl = c_dfs(w, dn, NULL);
return dn;
}
DIS_node * build_DIS_CON_tree(void) {
int w;
DIS_node * dnroot, * dn;
CON_list * child, * xchild;
List_o_links * lol, * xlol;
for (w=0; w<N_words; w++) {
	dfs_root_word[w] = -1;
}
dnroot = NULL;
for (w=0; w < N_words; w++) {
	if (dfs_root_word[w] == -1) {
	    dn = build_DIS_node(w);
	    if (dnroot == NULL) {
		dnroot = dn;
	    } else {
		for (child = dn->cl; child != NULL; child = xchild) {
		    xchild = child->next;
		    child->next = dnroot->cl;
		    dnroot->cl = child;
		}
		for (lol = dn->lol; lol != NULL; lol = xlol) {
		    xlol = lol->next;
		    lol->next = dnroot->lol;
		    dnroot->lol = lol;
		}
		xfree((void *) dn, sizeof(DIS_node));
	    }
	}
}
return dnroot;
}
int advance_CON(CON_node *);
int advance_DIS(DIS_node * dn) {
CON_list * cl;
for (cl = dn->cl; cl!=NULL; cl=cl->next) {
	if (advance_CON(cl->cn)) {
	    return TRUE;
	}
}
return FALSE;
}
int advance_CON(CON_node * cn) {
if (advance_DIS(cn->current->dn)) {
	return TRUE;
} else {
	if (cn->current->next == NULL) {
	    cn->current = cn->dl;
	    return FALSE;
	} else {
	    cn->current = cn->current->next;
	    return TRUE;
	}
}
}
typedef struct patch_element_struct Patch_element;
struct patch_element_struct {
char used;
char changed;
int newl;
int newr;
};
static Patch_element patch_array[MAX_LINKS];
void fill_patch_array_CON(CON_node *, Links_to_patch *);
void fill_patch_array_DIS(DIS_node * dn, Links_to_patch * ltp) {
CON_list * cl;
List_o_links * lol;
Links_to_patch * ltpx;
for (lol=dn->lol; lol != NULL; lol=lol->next) {
	patch_array[lol->link].used = TRUE;
}
if ((dn->cl == NULL) || (dn->cl->cn->word != dn->word)) {
	for (; ltp != NULL; ltp = ltpx) {
	    ltpx = ltp->next;
	    patch_array[ltp->link].changed = TRUE;
	    if (ltp->dir == 'l') {
		patch_array[ltp->link].newl = dn->word;
	    } else {
		patch_array[ltp->link].newr = dn->word;
	    }
	    xfree((void *) ltp, sizeof(Links_to_patch));
	}
}
for (cl=dn->cl; cl!=NULL; cl=cl->next) {
	fill_patch_array_CON(cl->cn, ltp);
	ltp = NULL;
}
}
void fill_patch_array_CON(CON_node * cn, Links_to_patch * ltp) {
List_o_links * lol;
Links_to_patch *ltpx;
for (lol=word_links[cn->word]; lol != NULL; lol = lol->next) {
	if (lol->dir == 0) {
	    ltpx = (Links_to_patch *) xalloc(sizeof(Links_to_patch));
	    ltpx->next = ltp;
	    ltp = ltpx;
	    ltp->new = cn->word;
	    ltp->link = lol->link;
	    if (lol->word > cn->word) {
		ltp->dir = 'l';
	    } else {
		ltp->dir = 'r';
	    }
	}
}
fill_patch_array_DIS(cn->current->dn, ltp);
}
void free_digraph(void) {
List_o_links * lol, *lolx;
int i;
for (i=0; i<N_words; i++) {
	for (lol=word_links[i]; lol!=NULL; lol=lolx) {
	    lolx = lol->next;
	    xfree((void *) lol, sizeof(List_o_links));
	}
}
}
void free_CON_tree(CON_node *);
void free_DIS_tree(DIS_node * dn) {
List_o_links * lol, *lolx;
CON_list *cl, *clx;
for (lol=dn->lol; lol!=NULL; lol=lolx) {
	lolx = lol->next;
	xfree((void *) lol, sizeof(List_o_links));
}
for (cl = dn->cl; cl!=NULL; cl=clx) {
	clx = cl->next;
	free_CON_tree(cl->cn);
	xfree((void *) cl, sizeof(CON_list));
}
xfree((void *) dn, sizeof(DIS_node));
}
void free_CON_tree(CON_node * cn) {
DIS_list *dl, *dlx;
for (dl = cn->dl; dl!=NULL; dl=dlx) {
	dlx = dl->next;
	free_DIS_tree(dl->dn);
	xfree((void *) dl, sizeof(DIS_list));
}
xfree((void *) cn, sizeof(CON_node));
}
void print_a_link(FILE *fp, int link) {
int j;
if (pp_link_array[link].l == 0 && left_wall_defined) {
	left_print_string(fp, LEFT_WALL_DISPLAY,"               ");
} else if (pp_link_array[link].l == N_words-1 && right_wall_defined) {
	left_print_string(fp, RIGHT_WALL_DISPLAY,"               ");	
} else {
	left_print_string(fp, chosen_words[pp_link_array[link].l], "               ");
}
left_print_string(fp, pp_link_array[link].lc->string, "     ");
j = pp_link_array[link].lc->label;
if (j<0) fprintf(fp, "   "); else fprintf(fp, "%3d",j);
fprintf(fp, "<---");
left_print_string(fp, pp_link_array[link].name, "-----");
fprintf(fp, "->  ");
left_print_string(fp, pp_link_array[link].rc->string, "     ");
j = pp_link_array[link].rc->label;
if (j<0) fprintf(fp, "   "); else fprintf(fp, "%3d",j);
fprintf(fp, "  %s", chosen_words[pp_link_array[link].r]);
fprintf(fp, "\n");
}
void print_links(FILE *fp) {
int link;
for (link=0; link<N_links; link++) {
	if (pp_link_array[link].l == -1) continue;
	fprintf(fp, "       ");
	print_a_link(fp, link);
}
fprintf(fp, "\n");
}
void print_links_and_domains(FILE *fp, PP_node * pp) {
int link, longest, j;
D_type_list * d;
Violation_list * v;
longest = 0;
for (link=0; link<N_links; link++) {
	if (pp_link_array[link].l == -1) continue;
	j = 0;
	for (d = pp->d_type_array[link]; d!=NULL; d=d->next) j++;
	if (j>longest) longest = j;
}
for (link=0; link<N_links; link++) {
	if (pp_link_array[link].l == -1) continue;
	j = 0;
	for (d = pp->d_type_array[link]; d!=NULL; d=d->next) {
	    fprintf(fp, " (%c)", d->type);
	    j++;
	}
	for (;j<longest; j++) {
	    fprintf(fp, "    ");
	}
	fprintf(fp, "   ");
	print_a_link(fp, link);
}
fprintf(fp, "\n");
if (pp->v != NULL) fprintf(fp, "P.P. violations:\n");
for (v=pp->v; v!=NULL; v=v->next) {
	fprintf(fp, "        %s\n", v->string);
}
}
static int visited[MAX_SENTENCE];
static int and_element_sizes[MAX_SENTENCE];
static int N_and_elements;
void and_dfs_full(int w) {
List_o_links *lol;
if (visited[w]) return;
visited[w] = TRUE;
and_element_sizes[N_and_elements]++;
for (lol = word_links[w]; lol != NULL; lol = lol->next) {
	if (lol->dir >= 0) {
	    and_dfs_full(lol->word);
	}
}
}
void and_dfs_commas(int w) {
List_o_links *lol;
if (visited[w]) return;
visited[w] = TRUE;
for (lol = word_links[w]; lol != NULL; lol = lol->next) {
	if (lol->dir == 1) {
	    if (strcmp(sentence[lol->word].string, ",")==0) {
		
		and_dfs_commas(lol->word);
	    } else {
		and_dfs_full(lol->word);
		N_and_elements++;
	    }
	}
}
}
int and_cost(void) {
int w, i, min, max, j, cost;
char * s;
cost = 0;
for(w = 0; w<N_words; w++) {
	s = sentence[w].string;
	if (is_conjunction[w]) {
	    N_and_elements = 0;
	    for(i=0; i<N_words; i++) {
		visited[i] = FALSE;
		and_element_sizes[i] = 0;
	    }
	    if (left_wall_defined) visited[0] = TRUE;
	    and_dfs_commas(w);
	    if (N_and_elements > 0) {
		min=MAX_SENTENCE;
		max=0;
		for (i=0; i<N_and_elements; i++) {
		    j = and_element_sizes[i];
		    if (j < min) min=j;
		    if (j > max) max=j;
		}
		cost += max-min;
	    }
	}
}
return cost;
}
int cost_for_length(int length) {
return length-1;
}
int link_cost(void) {
int lcost, i;
lcost =  0;
for (i=0; i<N_links; i++) {
	lcost += cost_for_length(link_array[i].r - link_array[i].l);
}
return lcost;
}
int N_null;
static int null_cost(void) {
return N_null;
}
int disjunct_cost(void) {
int lcost, i;
lcost =  0;
for (i=0; i<N_words; i++) {
if (chosen_disjuncts[i] != NULL)
	lcost += chosen_disjuncts[i]->cost;
}
return lcost;
}
int strictly_smaller_name(char * s, char * t) {
int strictness, ss, tt;
strictness = 0;
while ((*s!='\0') || (*t!='\0')) {
	if (*s == '\0') {
	    ss = '*';
	} else {
	    ss = *s;
	    s++;
	}
	if (*t == '\0') {
	    tt = '*';
	} else {
	    tt = *t;
	    t++;
	}
	if (ss == tt) continue;
	if ((tt == '*') || (ss == '^')) {
	    strictness++;
	} else {
	    return FALSE;
	}
}
return (strictness > 0);
}
void compute_link_names() {
int i;
for (i=0; i<N_links; i++) {
	link_array[i].name = intersect_strings(
	   link_array[i].lc->string, link_array[i].rc->string);
}
}
void compute_pp_link_names() {
int i;
char * s;
for (i=0; i<N_links; i++) {
	if (pp_link_array[i].l == -1) continue;
	if (!match(pp_link_array[i].lc, pp_link_array[i].rc)) {
	    pp_link_array[i].name = link_array[i].name;
	} else {
	    s = intersect_strings(pp_link_array[i].lc->string,
				  pp_link_array[i].rc->string);
	    if (strictly_smaller_name(s, link_array[i].name)) {
		pp_link_array[i].name = link_array[i].name;
	    } else {
		pp_link_array[i].name = s;
	    }
	}
}
}
Linkage_info analyze_fat_linkage(int should_print) {
int i;
int should_print_messages = TRUE;
Violation_list * v;
Linkage_info li;
DIS_node *d_root;
PP_node * pp, * accum;
D_type_list * dtl0, * dtl1;
build_digraph();
structure_violation = FALSE;
d_root = build_DIS_CON_tree();
li.N_violations = 0;
li.disjunct_cost = disjunct_cost();
li.null_cost = null_cost();
li.link_cost = link_cost();
if ((structure_violation && should_print && display_multiple) ||
	(should_print && display_fat)) {
	compute_link_names();
	for (i=0; i<N_links; i++) {
	    pp_link_array[i] = link_array[i];
	}
	print_links_graphically(stdout);
	if (display_links) print_links(stdout);
}
if (structure_violation) {
	if (display_links && display_bad) {
	    fprintf(stdout, "And structure violation.\n");
	}
	li.N_violations ++;
	li.and_cost = 0;
} else {
	li.and_cost = and_cost();
	compute_link_names();
	accum = (PP_node *) xalloc(sizeof(PP_node));
	accum->d_type_array = (D_type_list **) xalloc(N_links * sizeof(D_type_list *));
	accum->v = NULL;
	for (i=0; i<N_links; i++) accum->d_type_array[i] = NULL;
	for (;;) {
	    for (i=0; i<N_links; i++) {
		patch_array[i].used = patch_array[i].changed = FALSE;
		patch_array[i].newl = link_array[i].l;
		patch_array[i].newr = link_array[i].r;
		pp_link_array[i] = link_array[i];
	    }
	    fill_patch_array_DIS(d_root, NULL);
	
	
	
	    for (i=0; i<N_links; i++) {
		if (patch_array[i].changed || patch_array[i].used) {
		    pp_link_array[i].l = patch_array[i].newl;
		    pp_link_array[i].r = patch_array[i].newr;
		} else if ((dfs_root_word[link_array[i].l] != -1) &&
			   (dfs_root_word[link_array[i].r] != -1)) {
		    pp_link_array[i].l = -1;
		}
	    }
	
	    compute_pp_link_array_connectors();
	    compute_pp_link_names();
	    pp = post_process();
	    if (display_multiple && should_print) {
		
		
		print_links_graphically(stdout);
	    }
	    if (pp->v == NULL) {
		
		for (i=0; i<N_links; i++) {
		    if (pp_link_array[i].l == -1) continue;
		    if (accum->d_type_array[i] == NULL) {
			accum->d_type_array[i] = pp->d_type_array[i];
			pp->d_type_array[i] = NULL;
		    } else {
			dtl0 = pp->d_type_array[i];
			dtl1 = accum->d_type_array[i];
			while((dtl0 != NULL) && (dtl1 != NULL) &&
			      (dtl0->type == dtl1->type)) {
			    dtl0 = dtl0->next;
			    dtl1 = dtl1->next;
			}
			if ((dtl0 != NULL) || (dtl1 != NULL)) {
			    break;
			}
		    }
		}
		if (i != N_links) {
		    if (display_links && should_print_messages) {
			fprintf(stdout, "Incompatible domain ancestry\n");
			li.N_violations ++;
		    }
		    free_PP_node(pp);
		    break;
		}
	    } else {
		for (v=pp->v; v!=NULL; v=v->next) {
		    li.N_violations ++;
		}
	    }
	    free_PP_node(pp);
	
	
	
	    if (!advance_DIS(d_root)) break;
	}
	if (display_on && (li.N_violations != 0) && (verbosity > 1) && should_print_messages) {
	    fprintf(stdout, "P.P. violation in one part of conjunction.\n");
	}
	free_PP_node(accum);
}
free_digraph();
free_DIS_tree(d_root);
if (should_print) fflush(stdout);
return li;
}
Linkage_info analyze_thin_linkage(int should_print) {
int i;
Violation_list * v;
Linkage_info li;
PP_node * pp;
compute_link_names();
for (i=0; i<N_links; i++) {
	pp_link_array[i] = link_array[i];
}
pp = post_process();
if ((display_fat || display_multiple) && should_print) {
	print_links_graphically(stdout);
	if (display_links) print_links_and_domains(stdout, pp);
}
li.N_violations = 0;
li.and_cost = 0;
li.disjunct_cost = disjunct_cost();
li.null_cost = null_cost();
li.link_cost = link_cost();
for (v=pp->v; v!=NULL; v=v->next) li.N_violations ++;
free_PP_node(pp);
if (should_print) fflush(stdout);
return li;
}
/* 当前文件是D:\Read\and.c*/

typedef struct label_node_struct Label_node;
struct label_node_struct{
int label;
Label_node * next;
};
#define HT_SIZE (1<<10)
static Label_node * hash_table[HT_SIZE];
static Disjunct ** label_table;
static int LT_bound;
static int LT_size;
static int STAT_N_disjuncts;
static int STAT_calls_to_equality_test;
void init_LT(void) {
LT_bound = 200;
LT_size = 0;
label_table = (Disjunct **) xalloc(LT_bound * sizeof(Disjunct *));
}
void grow_LT(void) {
int i;
Disjunct ** new_table;
int new_LT_bound;
new_LT_bound = (3*LT_bound)/2;
new_table = (Disjunct **) xalloc(new_LT_bound * sizeof(Disjunct *));
for (i=0; i<LT_bound; i++) new_table[i] = label_table[i];
for (; i<new_LT_bound; i++) new_table[i] = NULL;
xfree((char *) label_table, LT_bound * sizeof(Disjunct*));
LT_bound = new_LT_bound;
label_table = new_table;
}
void init_HT(void) {
int i;
for (i=0; i<HT_SIZE; i++) {
	hash_table[i] = NULL;
}
}
void free_HT(void) {
int i;
Label_node * la, * la1;
for (i=0; i<HT_SIZE; i++) {
	for (la=hash_table[i]; la != NULL; la = la1) {
	    la1 = la->next;
	    xfree((char *)la, sizeof(Label_node));
	}
	hash_table[i] = NULL;
}
}
void free_LT(void) {
int i;
for (i=0; i<LT_size; i++) {
	free_disjuncts(label_table[i]);
}
xfree((char *) label_table, LT_bound * sizeof(Disjunct*));
LT_bound = 0;
LT_size = 0;
label_table = NULL;
}
void free_AND_tables(void) {
free_LT();
free_HT();
}
int and_connector_hash(Connector * c, int i) {
char * s;
s = c->string;
i = i + (i<<1) + randtable[(c->label + i) & (RTSIZE-1)];
while(isupper(*s)) {
	i = i + (i<<1) + randtable[(*s + i) & (RTSIZE-1)];
	s++;
}
return (i & (HT_SIZE-1));
}
int and_hash_disjunct(Disjunct *d) {
int i;
Connector *e;
i = 0;
for (e = d->left ; e != NULL; e = e->next) {
	i = and_connector_hash(e, i);
}
i = i + (i<<1) + randtable[i & (RTSIZE-1)];
for (e = d->right ; e != NULL; e = e->next) {
	i = and_connector_hash(e, i);
}
return (i & (HT_SIZE-1));
}
static int N_andable_hash_table;
static Connector ** andable_hash_table;
int andable_hash(char * s, int d) {
int i=d;
while(isupper(*s)) {
	i = i + (i<<1) + randtable[(*s + i) & (RTSIZE-1)];
	s++;
}
return (i & (N_andable_hash_table-1));
}
void fill_andable_hash_table(Exp * e) {
E_list * l;
Connector * c;
int h;
if (e->type == CONNECTOR_type) {
	c = (Connector *) xalloc(sizeof(Connector));
	c->string = e->u.string;
	c->label = NORMAL_LABEL;
	c->priority = THIN_priority;
	c->word = e->dir;
	h = andable_hash(c->string, c->word);
	c->next = andable_hash_table[h];
	andable_hash_table[h] = c;
} else {
	for (l=e->u.l; l!=NULL; l=l->next) {
	    fill_andable_hash_table(l->e);
	}
}
}	
void init_andable_hash_table(void) {
int i;
Exp * e;
e = dictionary_lookup(ANDABLE_CONNECTORS_WORD)->exp;
N_andable_hash_table = next_power_of_two_up(size_of_expression(e));
andable_hash_table =
(Connector **) xalloc(N_andable_hash_table * sizeof(Connector *));
for (i=0; i<N_andable_hash_table; i++) {
	andable_hash_table[i] = NULL;
}
fill_andable_hash_table(e);
}
int is_andable_connector(Connector * c, int d) {
int h;
Connector * c1;
if (!andable_defined) return TRUE;
h = andable_hash(c->string, d);
for (c1=andable_hash_table[h]; c1!=NULL; c1 = c1->next) {
	if (match(c1, c) && (d == c1->word)) return TRUE;
}
return FALSE;
}
int is_appropriate(Disjunct * d) {
Connector * c;
for (c = d->right; c!=NULL; c=c->next) {
	if (!is_andable_connector(c, '+')) return FALSE;
}
for (c = d->left; c!=NULL; c=c->next) {
	if (!is_andable_connector(c, '-')) return FALSE;
}
return TRUE;
}
int connector_types_equal(Connector * c1, Connector * c2) {
char * s, * t;
if (c1->label != c2->label) return FALSE;
s = c1->string;
t = c2->string;
while(isupper(*s) || isupper(*t)) {
	if (*s != *t) return FALSE;
	s++;
	t++;
}
return TRUE;
}
int disjunct_types_equal(Disjunct * d1, Disjunct * d2) {
Connector *e1, *e2;
e1 = d1->left;
e2 = d2->left;
while((e1!=NULL) && (e2!=NULL)) {
	if (!connector_types_equal(e1,e2)) break;
	e1 = e1->next;
	e2 = e2->next;
}
if ((e1!=NULL) || (e2!=NULL)) return FALSE;
e1 = d1->right;
e2 = d2->right;
while((e1!=NULL) && (e2!=NULL)) {
	if (!connector_types_equal(e1,e2)) break;
	e1 = e1->next;
	e2 = e2->next;
}
if ((e1!=NULL) || (e2!=NULL)) return FALSE;
return TRUE;
}
char * intersect_strings(char * s, char * t) {
int len, i, j, d;
char * u, *u0, *s0;
if (strcmp(s,t)==0) return s;
i = strlen(s);
j = strlen(t);
if (j > i) {
	u = s; s = t; t = u;
	len = j;
} else {
	len = i;
}
u0 = u = (char *) xalloc(len+1);
d = 0;
s0 = s;
while (*t != '\0') {
	if ((*s == *t) || (*t == '*')) {
	    *u = *s;
	} else {
	    d++;
	    if (*s == '*') *u = *t;
	    else *u = '^';
	}
	s++; t++; u++;
}
if (d==0) {
	xfree(u0, len+1);
	return s0;
} else {
	strcpy(u, s);
	free_this_string_later(u0, len+1);
	return u0;
}
}
int connectors_equal_AND(Connector *c1, Connector *c2) {
return (c1->label == c2->label) &&
	   (c1->multi == c2->multi) &&
(strcmp(c1->string, c2->string) == 0);
}
int disjuncts_equal_AND(Disjunct * d1, Disjunct * d2) {
Connector *e1, *e2;
STAT_calls_to_equality_test++;
e1 = d1->left;
e2 = d2->left;
while((e1!=NULL) && (e2!=NULL)) {
	if (!connectors_equal_AND(e1, e2)) break;
	e1 = e1->next;
	e2 = e2->next;
}
if ((e1!=NULL) || (e2!=NULL)) return FALSE;
e1 = d1->right;
e2 = d2->right;
while((e1!=NULL) && (e2!=NULL)) {
	if (!connectors_equal_AND(e1, e2)) break;
	e1 = e1->next;
	e2 = e2->next;
}
if ((e1!=NULL) || (e2!=NULL)) return FALSE;
return TRUE;
}
Disjunct * intersect_disjuncts(Disjunct * d1, Disjunct * d2) {
Disjunct * d;
Connector *c1, *c2, *c;
d = copy_disjunct(d1);
c = d->left;
c1 = d1->left;
c2 = d2->left;
while (c1!=NULL) {
	c->string = intersect_strings(c1->string, c2->string);
	c->multi = (c1->multi) && (c2->multi);
	c = c->next; c1 = c1->next; c2 = c2->next;
}
c = d->right;
c1 = d1->right;
c2 = d2->right;
while (c1!=NULL) {
	c->string = intersect_strings(c1->string, c2->string);
	c->multi = (c1->multi) && (c2->multi);
	c = c->next; c1 = c1->next; c2 = c2->next;
}
return d;
}
void put_disjunct_into_table(Disjunct *d) {
Disjunct *d1=NULL, *d2, *di, *d_copy;
Label_node * lp;
int h, k;
h = and_hash_disjunct(d);
for (lp = hash_table[h]; lp != NULL; lp = lp->next) {
	d1 = label_table[lp->label];
	if (disjunct_types_equal(d,d1)) break;
}
if (lp != NULL) {
	
	
	while(d1 != NULL) {
	    if (disjuncts_equal_AND(d1, d)) return;
	    d1 = d1->next;
	}
	
	d_copy = copy_disjunct(d);
	d_copy->cost = 0;
	k = lp->label;
	d2 = NULL;
	for (d1=label_table[k]; d1!=NULL; d1 = d1->next) {
	    di = intersect_disjuncts(d_copy, d1);
	    di->next = d2;
	    d2 = di;
	}
	d_copy->next = label_table[k];
	label_table[k] = d_copy;
	for (;d2 != NULL; d2 = di) {
	    di = d2->next;
	    for (d1 = label_table[k]; d1 != NULL; d1 = d1->next) {
		if (disjuncts_equal_AND(d1, d2)) break;
	    }
	    if (d1 == NULL) {
		STAT_N_disjuncts++;
		d2->next = label_table[k];
		label_table[k] = d2;
	    } else {
		d2->next = NULL;
		free_disjuncts(d2);
	    }
	}
} else {
	
	d_copy = copy_disjunct(d);
	d_copy->cost = 0;
	d_copy->next = NULL;
	if (LT_size == LT_bound) grow_LT();
	lp = (Label_node *) xalloc(sizeof(Label_node));
	lp->next = hash_table[h];
	hash_table[h] = lp;
	lp->label = LT_size;
	label_table[LT_size] = d_copy;
	LT_size++;
	STAT_N_disjuncts++;
}
}
void extract_all_fat_links(Disjunct * d) {
Connector * cl, * cr, *tl, *tr;
tl = d->left;
d->left = NULL;
for (cr = d->right; cr!=NULL; cr = cr->next) {
	tr = cr->next;
	cr->next = NULL;
	if (is_appropriate(d)) put_disjunct_into_table(d);
	cr->next = tr;
}
d->left = tl;
tr = d->right;
d->right = NULL;
for (cl = d->left; cl!=NULL; cl = cl->next) {
	tl = cl->next;
	cl->next = NULL;
	if (is_appropriate(d)) put_disjunct_into_table(d);
	cl->next = tl;
}
d->right = tr;
for (cl = d->left; cl!=NULL; cl = cl->next) {
	for (cr = d->right; cr!=NULL; cr = cr->next) {
	    tl = cl->next;
	    tr = cr->next;
	    cl->next = cr->next = NULL;
	    if (is_appropriate(d)) put_disjunct_into_table(d);
	    cl->next = tl;
	    cr->next = tr;
	}
}
}
char * stick_in_one_connector(char *s, Connector *c, int len) {
char * t;
for (t = c->string; isupper(*t); t++)
;
while (*t != '\0') {
	*s++ = *t++;
	len--;
}
while (len > 0) {
	*s++ = '*';
	len--;
}
if (c->multi) *s++ = '*'; else *s++ = '^';
*s = '\0';
return s;
}
void compute_matchers_for_a_label(int k) {
int * lengths;
int N_connectors, i, j, tot_len;
Connector * c;
Disjunct * d;
char *s, *os;
d = label_table[k];
N_connectors = 0;
for (c=d->left; c != NULL; c = c->next) N_connectors ++;
for (c=d->right; c != NULL; c = c->next) N_connectors ++;
lengths = (int *) xalloc(N_connectors*sizeof(int));
for (i=0; i<N_connectors; i++) lengths[i] = 0;
while(d != NULL) {
	i = 0;
	for (c=d->left; c != NULL; c = c->next) {
	    s = c->string;
	    while(isupper(*s)) s++;
	    j = strlen(s);
	    if (j > lengths[i]) lengths[i] = j;
	    i++;
	}
	for (c=d->right; c != NULL; c = c->next) {
	    s = c->string;
	    while(isupper(*s)) s++;
	    j = strlen(s);
	    if (j > lengths[i]) lengths[i] = j;
	    i++;
	}
	d = d->next;
}
tot_len = 0;
for (i=0; i<N_connectors; i++) tot_len += lengths[i]+1;
for (d = label_table[k]; d!= NULL; d = d->next) {
	i=0;
	os = s = (char *) xalloc(tot_len+1);
	free_this_string_later(s, tot_len+1);
	for (c=d->left; c != NULL; c = c->next) {
	    s = stick_in_one_connector(s, c, lengths[i]);
	    i++;
	}
	for (c=d->right; c != NULL; c = c->next) {
	    s = stick_in_one_connector(s, c, lengths[i]);
	    i++;
	}
	d->string = os;
}
xfree((char *)lengths, N_connectors*sizeof(int));
}
void build_conjunction_tables(void) {
int w;
int k;
Disjunct * d;
init_HT();
init_LT();
STAT_N_disjuncts = STAT_calls_to_equality_test = 0;
for (w=0; w<N_words; w++) {
	for (d=sentence[w].d; d!=NULL; d=d->next) {
	    extract_all_fat_links(d);
	}
}
for (k=0; k<LT_size; k++) {
	compute_matchers_for_a_label(k);
}
}
void print_AND_statistics(void) {
printf("Number of disjunct types (labels): %d\n", LT_size);
printf("Number of disjuncts in the table: %d\n", STAT_N_disjuncts);
printf("average list length: %f\n",
	   (float)STAT_N_disjuncts/LT_size);
printf("Number of equality tests: %d\n", STAT_calls_to_equality_test);
}
void connector_for_disjunct(Disjunct * d, Connector * c) {
int h;
Disjunct * d1=NULL;
Label_node * lp;
h = and_hash_disjunct(d);
for (lp = hash_table[h]; lp != NULL; lp = lp->next) {
	d1 = label_table[lp->label];
	if (disjunct_types_equal(d,d1)) break;
}
assert(lp!=NULL, "A disjunct I inserted was not there. (1)");
while(d1 != NULL) {
	if (disjuncts_equal_AND(d1, d)) break;
	d1 = d1->next;
}
assert(d1!=NULL, "A disjunct I inserted was not there. (2)");
c->label = lp->label;
c->string = d1->string;
c->priority = UP_priority;
c->multi = FALSE;
}
Disjunct * build_fat_link_substitutions(Disjunct *d) {
Connector * cl, * cr, *tl, *tr, *wc, work_connector;
Disjunct *d1, *wd, work_disjunct, *d_list;
if (d==NULL) return NULL;
wd = & work_disjunct;
wc = & work_connector;
d_list = NULL;
*wd = *d;
tl = d->left;
d->left = NULL;
for (cr = d->right; cr!=NULL; cr = cr->next) {
	tr = cr->next;
	cr->next = NULL;
	if (is_appropriate(d)) {
	    connector_for_disjunct(d,wc);
	    wd->left = tl;
	    wd->right = wc;
	    wc->next = tr;
	    d1 = copy_disjunct(wd);
	    d1->next = d_list;
	    d_list = d1;
	    wd->left = wc;
	    wc->next = tl;
	    wd->right = tr;
	    d1 = copy_disjunct(wd);
	    d1->next = d_list;
	    d_list = d1;
	}
	cr->next = tr;
}
d->left = tl;
tr = d->right;
d->right = NULL;
for (cl = d->left; cl!=NULL; cl = cl->next) {
	tl = cl->next;
	cl->next = NULL;
	if (is_appropriate(d)) {
	    connector_for_disjunct(d,wc);
	    wd->left = tl;
	    wd->right = wc;
	    wc->next = tr;
	    d1 = copy_disjunct(wd);
	    d1->next = d_list;
	    d_list = d1;
	    wd->left = wc;
	    wc->next = tl;
	    wd->right = tr;
	    d1 = copy_disjunct(wd);
	    d1->next = d_list;
	    d_list = d1;
	}
	cl->next = tl;
}
d->right = tr;
for (cl = d->left; cl!=NULL; cl = cl->next) {
	for (cr = d->right; cr!=NULL; cr = cr->next) {
	    tl = cl->next;
	    tr = cr->next;
	    cl->next = cr->next = NULL;
	    if (is_appropriate(d)) {
		connector_for_disjunct(d,wc);
		wd->left = tl;
		wd->right = wc;
		wc->next = tr;
		d1 = copy_disjunct(wd);
		d1->next = d_list;
		d_list = d1;
		wd->left = wc;
		wc->next = tl;
		wd->right = tr;
		d1 = copy_disjunct(wd);
		d1->next = d_list;
		d_list = d1;
	    }
	    cl->next = tl;
	    cr->next = tr;
	}
}
return d_list;
}
Disjunct * explode_disjunct_list(Disjunct *d) {
Disjunct *d1;
d1 = NULL;
for (; d!=NULL; d = d->next) {
d1 = catenate_disjuncts(d1, build_fat_link_substitutions(d));
}
return d1;
}
Disjunct * build_COMMA_disjunct_list(void) {
int lab;
Disjunct *d1, *d2, *d, work_disjunct, *wd;
Connector work_connector1, work_connector2, *c1, *c2;
Connector work_connector3, *c3;
c1 = & work_connector1;
c2 = & work_connector2;
c3 = & work_connector3;
wd = & work_disjunct;
d1 = NULL;
c1->next = NULL;
c2->next = c3;
c3->next = NULL;
c1->priority = c3->priority = DOWN_priority;
c2->priority = UP_priority;
c1->multi = c2->multi = c3->multi = FALSE;
wd->left = c1;
wd->right = c2;
wd->string = ",";
wd->next = NULL;
wd->cost = 0;
for (lab = 0; lab < LT_size; lab++) {
	for (d = label_table[lab]; d!=NULL; d=d->next) {
	    c1->string = c2->string = c3->string = d->string;
	    c1->label = c2->label = c3->label = lab;
	    d2 = copy_disjunct(wd);
	    d2->next = d1;
	    d1 = d2;
	}
}
return d1;
}
Disjunct * build_AND_disjunct_list(char * s) {
int lab;
Disjunct *d_list, *d1, *d3, *d, *d_copy;
Connector *c1, *c2, *c3;
d_list = NULL;
for (lab = 0; lab < LT_size; lab++) {
	for (d = label_table[lab]; d!=NULL; d=d->next) {
	    d1 = build_fat_link_substitutions(d);
	    d_copy = copy_disjunct(d);
	    d_copy->next = d1;
	    d1 = d_copy;
	    for(;d1 != NULL; d1 = d3) {
		d3 = d1->next;
		c1 = (Connector *) xalloc(sizeof (Connector));
		c2 = (Connector *) xalloc(sizeof (Connector));
		c1->next = NULL;
		c2->next = NULL;
		c1->priority = c2->priority = DOWN_priority;
		c1->multi = c2->multi = FALSE;
		c1->string = c2->string = d->string;
		c1->label = c2->label = lab;
	
		d1->string = s;
	
		if (d1->right == NULL) {
		    d1->right = c2;
		} else {
		    for (c3=d1->right; c3->next != NULL; c3 = c3->next)
		      ;
		    c3->next = c2;
		}
		if (d1->left == NULL) {
		    d1->left = c1;
		} else {
		    for (c3=d1->left; c3->next != NULL; c3 = c3->next)
		      ;
		    c3->next = c1;
		}
		d1->next = d_list;
		d_list = d1;
	    }
	}
}
#if defined PLURALIZATION
if (strcmp(s,"and")==0) {
	for (d1 = d_list; d1!=NULL; d1=d1->next) {
	    for (c1=d1->right; c1!=NULL; c1=c1->next) {
		if ((c1->string[0] == 'S') &&
		    ((c1->string[1]=='^') ||
		     (c1->string[1]=='s') ||
		     (c1->string[1]=='p') ||
		     (c1->string[1]=='\0'))) {
		    c1->string = "Sp";
		}
	    }
	    for (c1=d1->left; c1!=NULL; c1=c1->next) {
		if ((c1->string[0] == 'S') && (c1->string[1]=='I') &&
		    ((c1->string[2]=='^') ||
		     (c1->string[2]=='s') ||
		     (c1->string[2]=='p') ||
		     (c1->string[2]=='\0'))) {
		    c1->string = "SIp";
		}
	    }
	}
}
else if ((strcmp(s,"nor")==0) || (strcmp(s,"or")==0)) {
	for (d1 = d_list; d1!=NULL; d1=d1->next) {
	    for (c1=d1->right; c1!=NULL; c1=c1->next) {
		if ((c1->string[0] == 'S') &&
		    ((c1->string[1]=='^') ||
		     (c1->string[1]=='s') ||
		     (c1->string[1]=='p'))) {
		    c1->string = "S";		
		}
	    }
	    for (c1=d1->left; c1!=NULL; c1=c1->next) {
		if ((c1->string[0] == 'S') && (c1->string[1] == 'I') &&
		    ((c1->string[2]=='^') ||
		     (c1->string[2]=='s') ||
		     (c1->string[2]=='p'))) {
		    c1->string = "SI";		
		}
	    }
	}
}
#endif
return d_list;
}
typedef struct Image_node_struct Image_node;
struct Image_node_struct {
Image_node * next;
Connector * c;
int place;
};
Image_node * image_array[MAX_SENTENCE];
char has_fat_down[MAX_SENTENCE];
int set_has_fat_down(void) {
int link, w, N_fat;
N_fat = 0;
for (w=0; w<N_words; w++) {
	has_fat_down[w] = FALSE;
}
for (link=0; link<N_links; link++) {
	if (link_array[link].lc->priority == DOWN_priority) {
	    N_fat ++;
	    has_fat_down[link_array[link].l] = TRUE;
	} else if (link_array[link].rc->priority == DOWN_priority) {
	    N_fat ++;
	    has_fat_down[link_array[link].r] = TRUE;
	}
}
return (N_fat > 0);
}
void free_image_array(void) {
int w;
Image_node * in, * inx;
for (w=0; w<N_words; w++) {
	for (in=image_array[w]; in!=NULL; in=inx) {
	    inx = in->next;
	    xfree((char *)in, sizeof(Image_node));
	}
}
}	
void build_image_array(void) {
int link, end, word;
Connector * this_end_con, *other_end_con, * upcon, * updiscon, *clist;
Disjunct * dis, * updis;
Image_node * in;
for (word=0; word<N_words; word++) {
	image_array[word] = NULL;
}
for (end = -1; end <= 1; end += 2) {
	for (link=0; link<N_links; link++) {
	    if (end<0) {
		word = link_array[link].l;
		if (!has_fat_down[word]) continue;
		this_end_con = link_array[link].lc;
		other_end_con = link_array[link].rc;
		dis = chosen_disjuncts[word];
		clist = dis->right;
	    } else {
		word = link_array[link].r;
		if (!has_fat_down[word]) continue;
		this_end_con = link_array[link].rc;
		other_end_con = link_array[link].lc;
		dis = chosen_disjuncts[word];
		clist = dis->left;
	    }
	    if (this_end_con->priority == DOWN_priority) continue;
	    if ((this_end_con->label != NORMAL_LABEL) &&
		(this_end_con->label < 0)) continue;
	
	    in = (Image_node *) xalloc(sizeof(Image_node));
	    in->next = image_array[word];
	    image_array[word] = in;
	    in->c = other_end_con;
	
	    if (this_end_con->priority == UP_priority) {
		in->place = 0;
	    } else {
		in->place = 1;
		if ((dis->left != NULL) &&
		    (dis->left->priority == UP_priority)) {
		    upcon = dis->left;
		} else if ((dis->right != NULL) &&
			   (dis->right->priority == UP_priority)) {
		    upcon = dis->right;
		} else {
		    upcon = NULL;
		}
		if (upcon != NULL) {
		    updis = label_table[upcon->label];
		    if (end > 0) {
			updiscon = updis->left;
		    } else {
			updiscon = updis->right;
		    }
		    for (;updiscon != NULL; updiscon = updiscon->next) {
			in->place ++;
		    }
		}
		for (; clist != this_end_con; clist = clist->next) {
		    if (clist->label < 0) in->place++;
		}
		in->place = in->place * (-end);
	    }
	}
}
}
int strictly_smaller(char * s, char * t) {
int strictness;
strictness = 0;
for (;(*s!='\0') && (*t!='\0'); s++,t++) {
	if (*s == *t) continue;
	if ((*t == '*') || (*s == '^')) {
	    strictness++;
	} else {
	    return FALSE;
	}
}
assert(! ((*s!='\0') || (*t!='\0')), "s and t should be the same length!");
return (strictness > 0);
}
Disjunct * find_subdisjunct(Disjunct * dis, int label) {
Disjunct * d;
Connector * cx, *cy;
for (d=label_table[label]; d!=NULL; d=d->next) {
	for (cx=d->left, cy=dis->left; cx!=NULL; cx=cx->next,cy=cy->next) {
	    if ((strcmp(cx->string, cy->string) != 0) ||
		(cx->multi != cy->multi)) break;
	}
	if (cx!=NULL) continue;
	for (cx=d->right, cy=dis->right; cx!=NULL; cx=cx->next,cy=cy->next) {
	    if ((strcmp(cx->string, cy->string) != 0) ||
		(cx->multi != cy->multi)) break;
	}
	if (cx==NULL) break;
}
assert(d!=NULL, "Never found subdisjunct");
return d;
}
int is_canonical_linkage(void) {
int w, d_label=0, place;
Connector *d_c, *c, dummy_connector, *upcon;
Disjunct *dis, *chosen_d;
Image_node * in;
dummy_connector.priority = UP_priority;
build_image_array();
for (w=0; w<N_words; w++) {
	if (!has_fat_down[w]) continue;
	chosen_d = chosen_disjuncts[w];
	for (d_c = chosen_d->left; d_c!=NULL; d_c=d_c->next) {
	    if (d_c->priority == DOWN_priority) {
		d_label = d_c->label;
		break;
	    }
	}
	assert(d_c != NULL, "Should have found the down link.");
	if ((chosen_d->left != NULL) &&
	    (chosen_d->left->priority == UP_priority)) {
	    upcon = chosen_d->left;
	} else if ((chosen_d->right != NULL) &&
		   (chosen_d->right->priority == UP_priority)) {
	    upcon = chosen_d->right;
	} else {
	    upcon = NULL;
	}
	
	
	
	for (dis=label_table[d_label]; dis!=NULL; dis=dis->next) {
	
	
	    if(!strictly_smaller(dis->string, d_c->string)) continue;
	
	    for (in=image_array[w]; in!=NULL; in=in->next) {
		place = in->place;
		if (place == 0) {
	
		    assert(upcon != NULL, "Should have found an up link");
		    dummy_connector.label = upcon->label;
		
		    if (upcon->label == d_label) {
			dummy_connector.string = dis->string;
		    } else {
			dummy_connector.string =
			  find_subdisjunct(dis, upcon->label)->string;
		    }
		    if (!match(&dummy_connector, in->c)) break;
		} else if (place > 0) {
		    for (c=dis->right; place > 1; place--) {
			c = c->next;
		    }
		    if (!match(c, in->c)) break;
		} else {
		    for (c=dis->left; place < -1; place++) {
			c = c->next;
		    }
		    if (!match(c, in->c)) break;
		}
	    }
	    if (in == NULL) break;
	}
	if (dis != NULL) break;
	
}
free_image_array();
return (w == N_words);
}
void compute_pp_link_array_connectors(void) {
int link, end, word, place;
Connector * this_end_con, * upcon, * updiscon, *clist, *con, *mycon;
Disjunct * dis, * updis, *mydis;
for (end = -1; end <= 1; end += 2) {
	for (link=0; link<N_links; link++) {
	    if (pp_link_array[link].l == -1) continue;
	    if (end<0) {
		word = link_array[link].l;
		if (!has_fat_down[word]) continue;
		this_end_con = link_array[link].lc;
		dis = chosen_disjuncts[word];
		mydis = chosen_disjuncts[pp_link_array[link].l];
		clist = dis->right;
	    } else {
		word = link_array[link].r;
		if (!has_fat_down[word]) continue;
		this_end_con = link_array[link].rc;
		dis = chosen_disjuncts[word];
		mydis = chosen_disjuncts[pp_link_array[link].r];
		clist = dis->left;
	    }
	    if (this_end_con->label != NORMAL_LABEL) continue;
	
	
	    place = 0;
	    if ((dis->left != NULL) &&
		(dis->left->priority == UP_priority)) {
		upcon = dis->left;
	    } else if ((dis->right != NULL) &&
		       (dis->right->priority == UP_priority)) {
		upcon = dis->right;
	    } else {
		upcon = NULL;
	    }
	    if (upcon != NULL) {
		updis = label_table[upcon->label];
		if (end > 0) {
		    updiscon = updis->left;
		} else {
		    updiscon = updis->right;
		}
		for (;updiscon != NULL; updiscon = updiscon->next) {
		    place ++;
		}
	    }
	    for (; clist != this_end_con; clist = clist->next) {
		if (clist->label < 0) place++;
	    }
	
	
	    if ((mydis->left != NULL) &&
		(mydis->left->priority == UP_priority)) {
		mycon = mydis->left;
	    } else if ((mydis->right != NULL) &&
		       (mydis->right->priority == UP_priority)) {
		mycon = mydis->right;
	    } else {
		printf("word = %d\n", word);
		printf("fat link: [%d, %d]\n", link_array[link].l, link_array[link].r);
		printf("thin link: [%d, %d]\n", pp_link_array[link].l, pp_link_array[link].r);
		assert(FALSE, "There should be a fat UP link here");
	    }
	    for (dis=label_table[mycon->label]; dis != NULL; dis=dis->next) {
		if (dis->string == mycon->string) break;
	    }
	    assert(dis!=NULL, "Should have found this connector string");
	
	    if (end < 0) {
		for (con = dis->right; place > 0; place--, con=con->next);
		pp_link_array[link].lc = con;
	    } else {
		for (con = dis->left; place > 0; place--, con=con->next);
		pp_link_array[link].rc = con;
	    }
	}
}
}
/* 当前文件是D:\Read\build-disjuncts.c*/

typedef struct Tconnector_struct Tconnector;
struct Tconnector_struct{
char multi;
char dir;
Tconnector * next;
char * string;
};
typedef struct clause_struct Clause;
struct clause_struct {
Clause * next;
int cost;
int maxcost;
Tconnector * c;
};
Tconnector * copy_Tconnectors(Tconnector * c) {
Tconnector *c1;
if (c == NULL) return NULL;
c1 = (Tconnector *) xalloc(sizeof(Tconnector));
*c1 = *c;
c1->next = copy_Tconnectors(c->next);
return c1;
}
void free_Tconnectors(Tconnector *e) {
Tconnector * n;
for(;e != NULL; e=n) {
	n = e->next;
	xfree((char *)e, sizeof(Tconnector));
}
}
void free_clause_list(Clause *c) {
Clause *c1;
while (c != NULL) {
	c1 = c->next;
	free_Tconnectors(c->c);
	xfree((char *)c, sizeof(Clause));
	c = c1;
}
}
Clause * copy_clause(Clause * d) {
Clause * d1;
if (d == NULL) return NULL;
d1 = (Clause *) xalloc(sizeof(Clause));
*d1 = *d;
d1->next = NULL;
d1->c = copy_Tconnectors(d->c);
return d1;
}
Tconnector * Treverse(Tconnector *e) {
Tconnector * head, *x;
head = NULL;
while (e != NULL) {
	x = e->next;
	e->next = head;
	head = e;
	e = x;
}
return head;
}
Connector * reverse(Connector *e) {
Connector * head, *x;
head = NULL;
while (e != NULL) {
	x = e->next;
	e->next = head;
	head = e;
	e = x;
}
return head;
}
Tconnector * catenate(Tconnector * e1, Tconnector * e2) {
Tconnector * e, * head;
head = NULL;
for (;e1 != NULL; e1 = e1->next) {
	e = (Tconnector *) xalloc(sizeof(Tconnector));
	*e = *e1;
	e->next = head;
	head = e;
}
for (;e2 != NULL; e2 = e2->next) {
	e = (Tconnector *) xalloc(sizeof(Tconnector));
	*e = *e2;
	e->next = head;
	head = e;
}
return Treverse(head);
}
Tconnector * build_terminal(Exp * e) {
Tconnector * c;
c = (Tconnector *) xalloc(sizeof(Tconnector));
c->string = e->u.string;
c->multi = e->multi;
c->dir = e->dir;
c->next = NULL;
return c;
}
int maxcost_of_expression(Exp *e) {
E_list * e_list;
int m, m1;
m = 0;
if ((e->type == AND_type) || (e->type == OR_type)) {
	for (e_list = e->u.l; e_list != NULL; e_list = e_list->next) {
	    m1 = maxcost_of_expression(e_list->e);
	    m = MAX(m, m1);
	}
}
return (m + e->cost);
}
int maxcost_of_sentence(void) {
X_node * x;
int w, m, m1;
m = 0;
for (w=0; w<N_words; w++) {
	for (x=sentence[w].x; x!=NULL; x = x->next){
	    m1 = maxcost_of_expression(x->exp),
	    m = MAX(m, m1);
	}
}
return m;
}
Clause * build_clause(Exp *e, int cost_cutoff) {
Clause *c=NULL, *c1, *c2, *c3, *c4, *c_head;
E_list * e_list;
assert(e != NULL, "build_clause called with null parameter");
if (e->type == AND_type) {
	c1 = (Clause *) xalloc(sizeof (Clause));
	c1->c = NULL;
	c1->next = NULL;
	c1->cost = 0;
	c1->maxcost = 0 ;
	for (e_list = e->u.l; e_list != NULL; e_list = e_list->next) {
	    c2 = build_clause(e_list->e, cost_cutoff);
	    c_head = NULL;
	    for (c3 = c1; c3 != NULL; c3 = c3->next) {
		for (c4 = c2; c4 != NULL; c4 = c4->next) {
		    c = (Clause *) xalloc(sizeof (Clause));
		    c->cost = c3->cost + c4->cost;
		    c->maxcost = MAX(c3->maxcost,c4->maxcost);
		    c->c = catenate(c3->c, c4->c);
		    c->next = c_head;
		    c_head = c;
		}
	    }
	    free_clause_list(c1);
	    free_clause_list(c2);
	    c1 = c_head;
	}
	c = c1;
} else if (e->type == OR_type) {
	
	c = NULL;
	for (e_list = e->u.l; e_list != NULL; e_list = e_list->next) {
	    c1 = build_clause(e_list->e, cost_cutoff);
	    while(c1 != NULL) {
		c3 = c1->next;
		c1->next = c;
		c = c1;
		c1 = c3;
	    }
	}
} else if (e->type == CONNECTOR_type) {
	c = (Clause *) xalloc(sizeof(Clause));
	c->c = build_terminal(e);
	c->cost = 0;
	c->maxcost = 0;
	c->next = NULL;
} else {
	assert(FALSE, "an expression node with no type");
}
for (c1=c; c1!=NULL; c1 = c1->next) {
	c1->cost += e->cost;
	c1->maxcost += e->cost;
}
return c;
}
void print_connector_list(Connector * e) {
for (;e != NULL; e=e->next) {
	printf("%s",e->string);
	if (e->label != NORMAL_LABEL) {
	    printf("%3d", e->label);
	} else {
	    printf("   ");
	}
	if (e->next != NULL) printf(" ");
}
}
void print_Tconnector_list(Tconnector * e) {
for (;e != NULL; e=e->next) {
	if (e->multi) printf("@");
	printf("%s",e->string);
	printf("%c", e->dir);
	if (e->next != NULL) printf(" ");
}
}
void print_clause_list(Clause * c) {
for (;c != NULL; c=c->next) {
	printf("  Clause: ");
	printf("(%2d, %2d)", c->cost, c->maxcost);
	print_Tconnector_list(c->c);
	printf("\n");
}
}
void print_disjunct_list(Disjunct * c) {
for (;c != NULL; c=c->next) {
	printf("%10s: ", c->string);
	printf("(%2d)", c->cost);
	print_connector_list(c->left);
	printf(" <--> ");
	print_connector_list(c->right);
	printf("\n");
}
}
Connector * extract_connectors(Tconnector *e, int c) {
Connector *e1;
if (e == NULL) return NULL;
if (e->dir == c) {
	e1 = (Connector *) xalloc(sizeof(Connector));
	e1->next = extract_connectors(e->next,c);
	e1->multi = e->multi;
	e1->string = e->string;
	e1->label = NORMAL_LABEL;
	e1->priority = THIN_priority;
	e1->word = 0;
	return e1;
} else {
	return extract_connectors(e->next,c);
}
}	
Disjunct * build_disjunct(Clause * cl, char * string, int cost_cutoff) {
Disjunct *dis, *ndis;
dis = NULL;
for (;cl != NULL; cl=cl->next) {
	if (cl->maxcost <= cost_cutoff) {
	    ndis = (Disjunct *) xalloc(sizeof(Disjunct));
	    ndis->left = reverse(extract_connectors(cl->c, '-'));
	    ndis->right = reverse(extract_connectors(cl->c, '+'));
	    ndis->string = string;
	    ndis->cost = cl->cost;
	    ndis->next = dis;
	    dis = ndis;
	}
}
return dis;
}
Disjunct * build_disjuncts_for_X_node(X_node * x, int cost_cutoff) {
Clause *c ;
Disjunct * dis;
c = build_clause(x->exp, cost_cutoff);
dis = build_disjunct(c, x->string, cost_cutoff);
free_clause_list(c);
return dis;
}
Disjunct * build_disjuncts_for_dict_node(Dict_node *dn) {
Clause *c ;
Disjunct * dis;
c = build_clause(dn->exp, NOCUTOFF);
dis = build_disjunct(c, dn->string, NOCUTOFF);
free_clause_list(c);
return dis;
}
#if 0
OBS
OBS Disjunct * build_word_disjuncts(char * s) {
OBS
OBS     Dict_node * dn;
OBS     Disjunct * dis;
OBS
OBS     dn = dictionary_lookup(s);
OBS
OBS
OBS     dis = NULL;
OBS
OBS     while (dn != NULL) {
OBS 	dis = catenate_disjuncts(build_disjuncts_for_dict_node(dn), dis);
OBS 	dn = dn->right;
OBS     }
OBS
OBS     return dis;
OBS }
#endif
X_node * build_word_expressions(char * s) {
Dict_node * dn;
X_node * x, * y;
dn = dictionary_lookup(s);
x = NULL;
while (dn != NULL) {
	y = (X_node *) xalloc(sizeof(X_node));
	y->next = x;
	x = y;
	x->exp = copy_Exp(dn->exp);
	x->string = dn->string;
	dn = dn->right;
}
return x;
}
void build_sentence_disjuncts(int cost_cutoff) {
Disjunct * d;
X_node * x;
int w;
for (w=0; w<N_words; w++) {
	d = NULL;
	for (x=sentence[w].x; x!=NULL; x = x->next){
	    d = catenate_disjuncts(build_disjuncts_for_X_node(x, cost_cutoff),d);
	}
	sentence[w].d = d;
}
}
/* 当前文件是D:\Read\extract-links.c*/
/*
Link link_array[MAX_LINKS];
int N_links;
char forgiving;
Disjunct * chosen_disjuncts[MAX_SENTENCE];*/
void issue_link(Disjunct *ld, Disjunct * rd, int lw, int rw,
		Connector * lc, Connector * rc) {
link_array[N_links].l = lw;
link_array[N_links].r = rw;
link_array[N_links].lc = lc;
link_array[N_links].rc = rc;
N_links++;
chosen_disjuncts[lw] = ld;
chosen_disjuncts[rw] = rd;
}
int magic(int lw, int rw, Connector *le, Connector *re, int cost) {
int count;
if (cost < 0) return 0;
count = table_lookup(lw, rw, le, re, cost);
if (count < 0) return 0; else return count;
}
void list_links(Disjunct *ld, Disjunct * rd, int lw, int rw,
Connector *le, Connector *re, int cost, int index) {
Disjunct * d;
int leftcount, rightcount, total;
int i, x, delta;
int lml=0, lmr=0, rml=0, rmr=0;
int lc, rc, lindex, rindex;
int lcost, rcost;
int w, start_word, end_word;
Match_node * m, *m1;
if (rw == 1+lw) {
	assert((le == NULL) && (re == NULL) && (index == 0),
	       "Error encountered while extracting links.");
	return;
}
if (cost < 0) return;
if ((le == NULL) && (re == NULL)) {
	total = 0;
	w = lw+1;
	for (d = sentence[w].d; d != NULL; d = d->next) {
	    if (d->left == NULL) {
		i = magic(w, rw, d->right, re, cost-1);
		total += i;
		if ((total-i <= index) && (total > index)) {
		    list_links(d, rd, w, rw, d->right, re, cost-1, index-total+i);
		}
	    }
	}
	i = magic(w, rw, NULL, NULL, cost-1);
	total += i;
	if ((total - i <= index) && (total > index)) {
	    list_links(NULL, rd, w, rw, NULL, re, cost-1, index-total+i);
	}
	return;
}
total = 0;
if (le == NULL) {
	start_word = lw+1;
} else {
	start_word = le->word;
}
if (re == NULL) {
	end_word = MIN(rw-1, lw+maxlinklength);
} else {
	end_word = re->word;
}
for (w=start_word; w <= end_word; w++) {
	m1 = m = form_match_list(w, le, lw, re, rw);
	for (; m!=NULL; m=m->next) {
	    d = m->d;
	    for (lcost = 0; lcost <= cost; lcost++) {
		rcost = cost-lcost;
		
		if ((le != NULL) && (d->left != NULL) && match(le, d->left)) {
		    lml = le->multi;
		    lmr = d->left->multi;
		    leftcount = magic(lw, w, le->next, d->left->next, lcost);
		    if (lml) leftcount += magic(lw, w, le, d->left->next, lcost);
		    if (lmr) leftcount += magic(lw, w, le->next, d->left, lcost);
		    if (lml&&lmr) leftcount += magic(lw, w, le, d->left, lcost);
		} else {
		    leftcount = 0;
		}
		if ((d->right != NULL) && (re != NULL) && match(d->right, re)) {
		    rml = d->right->multi;
		    rmr = re->multi;
		    rightcount = magic(w, rw, d->right->next,re->next, rcost);
		    if (rml) rightcount+= magic(w, rw, d->right, re->next, rcost);
		    if (rmr) rightcount+= magic(w, rw, d->right->next, re, rcost);
		    if (rml&&rmr) rightcount+= magic(w, rw, d->right, re, rcost);
		} else {
		    rightcount = 0;
		}
		i = leftcount * rightcount;
		total += i;
		
		if ((total-i <= index) && (total > index)) {
		    x = index-total+i;
		    lindex = x / rightcount;
		    rindex = x % rightcount;
		    lc = 0;
		    delta = magic(lw, w, le->next, d->left->next, lcost);
		    lc += delta;
		    if (lc > lindex) {
			issue_link(ld, d, lw, w, le, d->left);
			list_links(ld, d, lw, w, le->next, d->left->next, lcost, lindex-lc+delta);
		    }
		    if (lml) delta = magic(lw, w, le, d->left->next, lcost);
		    else delta = 0;
		    lc += delta;
		    if ((lc-delta <= lindex) && (lc > lindex)) {
			issue_link(ld, d, lw, w, le, d->left);
			list_links(ld, d, lw, w, le, d->left->next, lcost, lindex-lc+delta);
		    }
		    if (lmr) delta = magic(lw, w, le->next, d->left, lcost);
		    else delta=0;
		    lc += delta;
		    if ((lc-delta <=lindex) && lc > lindex) {
			issue_link(ld, d, lw, w, le, d->left);
			list_links(ld, d, lw, w, le->next, d->left, lcost, lindex-lc+delta);
		    }
		    if (lml&&lmr) delta = magic(lw, w, le, d->left, lcost);
		    else delta = 0;
		    lc += delta;
		    if ((lc-delta <=lindex) && lc > lindex) {
			issue_link(ld, d, lw, w, le, d->left);
			list_links(ld, d, lw, w, le, d->left, lcost, lindex-lc+delta);
		    }
		    rc = 0;
		    delta = magic(w, rw, d->right->next,re->next, rcost);
		    rc += delta;
		    if (rc > rindex) {
			issue_link(d, rd, w, rw, d->right, re);
			list_links(d, rd, w, rw, d->right->next, re->next, rcost, rindex-rc+delta);
		    }
		    if (rml) delta = magic(w, rw, d->right, re->next, rcost);
		    else delta = 0;
		    rc += delta;
		    if ((rc-delta <= rindex) && rc > rindex) {
			issue_link(d, rd, w, rw, d->right, re);
			list_links(d, rd, w, rw, d->right, re->next, rcost, rindex-rc+delta);
		    }
		    if (rmr) delta = magic(w, rw, d->right->next, re, rcost);
		    else delta = 0;
		    rc += delta;
		    if ((rc-delta <= rindex) && rc > rindex) {
			issue_link(d, rd, w, rw, d->right, re);
			list_links(d, rd, w, rw, d->right->next, re, rcost, rindex-rc+delta);
		    }
		    if (rml&&rmr) delta = magic(w, rw, d->right, re, rcost);
		    else delta = 0;
		    rc += delta;
		    if ((rc-delta <= rindex) && rc > rindex) {
			issue_link(d, rd, w, rw, d->right, re);
			list_links(d, rd, w, rw, d->right, re, rcost, rindex-rc+delta);
		    }
		}
		
		if (leftcount > 0) {
		    i = leftcount * magic(w, rw, d->right, re, rcost);
		} else {
		    i = 0;
		}
		total += i;
		if ((total-i <= index) && (total > index)) {
		    x = index-total+i;
		    lindex = x % leftcount;
		    rindex = x / leftcount;
		    lc = 0;
		    delta = magic(lw, w, le->next, d->left->next, lcost);
		    lc += delta;
		    if (lc > lindex) {
			issue_link(ld, d, lw, w, le, d->left);
			list_links(ld, d, lw, w, le->next,d->left->next, lcost, lindex-lc+delta);
		    }
		    if (lml) delta = magic(lw, w, le, d->left->next, lcost);
		    else delta = 0;
		    lc += delta;
		    if ((lc-delta <= lindex) && (lc > lindex)) {
			issue_link(ld, d, lw, w, le, d->left);
			list_links(ld, d, lw, w, le, d->left->next, lcost, lindex-lc+delta);
		    }
		    if (lmr) delta = magic(lw, w, le->next, d->left, lcost);
		    else delta=0;
		    lc += delta;
		    if ((lc-delta <=lindex) && lc > lindex) {
			issue_link(ld, d, lw, w, le, d->left);
			list_links(ld, d, lw, w, le->next, d->left, lcost, lindex-lc+delta);
		    }
		    if (lml&&lmr) delta = magic(lw, w, le, d->left, lcost);
		    else delta = 0;
		    lc += delta;
		    if ((lc-delta <=lindex) && lc > lindex) {
			issue_link(ld, d, lw, w, le, d->left);
			list_links(ld, d, lw, w, le, d->left, lcost, lindex-lc+delta);
		    }
		
		    list_links(d, rd, w, rw, d->right, re, rcost, rindex);
		}
		if ((le == NULL) && (rightcount > 0)) {
		    i = rightcount * magic(lw, w, le, d->left, lcost);
		} else {
		    i = 0;
		}
		total += i;
		if ((total-i <= index) && (total > index)) {
		    x = index-total+i;
		    rindex = x % rightcount;
		    lindex = x / rightcount;
		
		    rc = 0;
		    delta = magic(w, rw, d->right->next,re->next, rcost);
		    rc += delta;
		    if (rc > rindex) {
			issue_link(d, rd, w, rw, d->right, re);
			list_links(d, rd, w, rw, d->right->next, re->next, rcost, rindex-rc+delta);
		    }
		    if (rml) delta = magic(w, rw, d->right, re->next, rcost);
		    else delta = 0;
		    rc += delta;
		    if ((rc-delta <= rindex) && rc > rindex) {
			issue_link(d, rd, w, rw, d->right, re);
			list_links(d, rd, w, rw, d->right, re->next, rcost, rindex-rc+delta);
		    }
		    if (rmr) delta = magic(w, rw, d->right->next, re, rcost);
		    else delta = 0;
		    rc += delta;
		    if ((rc-delta <= rindex) && rc > rindex) {
			issue_link(d, rd, w, rw, d->right, re);
			list_links(d, rd, w, rw, d->right->next, re, rcost, rindex-rc+delta);
		    }
		    if (rml&&rmr) delta = magic(w, rw, d->right, re, rcost);
		    else delta = 0;
		    rc += delta;
		    if ((rc-delta <= rindex) && rc > rindex) {
			issue_link(d, rd, w, rw, d->right, re);
			list_links(d, rd, w, rw, d->right, re, rcost, rindex-rc+delta);
		    }
		    list_links(ld, d, lw, w, le, d->left, lcost, lindex);
		}
	    }
	}
	put_match_list(m1);
}
}
void initialize_links(void) {
int i;
for (i=0; i<N_words; ++i) {
	chosen_disjuncts[i] = NULL;
}
}
void extract_links(int index, int cost) {
Disjunct * dis;
int total, c=0;
N_links = 0;
total = 0;
initialize_links();
for (dis = sentence[0].d; dis != NULL; dis = dis->next) {
	if (dis->left == NULL) {
	    c = magic(0, N_words, dis->right, NULL, cost);
	    total += c;
	    if (total > index) break;
	}	
}
if (total > index) {
	list_links(dis, NULL, 0, N_words, dis->right, NULL, cost, index-total+c);
} else {
	c = magic(0, N_words, NULL, NULL, cost);
	total += c;
	list_links(NULL, NULL, 0, N_words, NULL, NULL, cost, index-total+c);
}
}
/* 当前文件是D:\Read\fast-match.c*/

static int match_cost;
int left_disjunct_list_length(Disjunct * d) {
int i;
for (i=0; d!=NULL; d=d->next) {
	if (d->left != NULL) i++;
}
return i;
}
int right_disjunct_list_length(Disjunct * d) {
int i;
for (i=0; d!=NULL; d=d->next) {
	if (d->right != NULL) i++;
}
return i;
}
static int l_table_size[MAX_SENTENCE];
static int r_table_size[MAX_SENTENCE];
static Match_node ** l_table[MAX_SENTENCE];
static Match_node ** r_table[MAX_SENTENCE];
static Match_node * mn_free_list = NULL;
Match_node * get_match_node(void) {
Match_node * m;
if (mn_free_list != NULL) {
	m = mn_free_list;
	mn_free_list = m->next;
} else {
	m = (Match_node *) xalloc(sizeof(Match_node));
}
return m;
}
void put_match_list(Match_node *m) {
Match_node * xm;
for (; m != NULL; m = xm) {
	xm = m->next;
	m->next = mn_free_list;
	mn_free_list = m;
}
}
void free_match_list(Match_node * t) {
Match_node *xt;
for (; t!=NULL; t=xt) {
	xt = t->next;
	xfree((char *)t, sizeof(Match_node));
}
}
void free_fast_matcher() {
int w;
int i;
if (verbosity > 1) printf("%d Match cost\n", match_cost);
for (w=0; w<N_words; w++) {
	for (i=0; i<l_table_size[w]; i++) {
	    free_match_list(l_table[w][i]);
	}
	xfree((char *)l_table[w], l_table_size[w] * sizeof (Match_node *));
	for (i=0; i<r_table_size[w]; i++) {
	    free_match_list(r_table[w][i]);
	}
	xfree((char *)r_table[w], r_table_size[w] * sizeof (Match_node *));
}
free_match_list(mn_free_list);
mn_free_list = NULL;
}
int fast_match_hash(Connector * c) {
char *s;
int i;
i = randtable[c->label & (RTSIZE-1)];
s = c->string;
while(isupper(*s)) {
	i = i + (i<<1) + randtable[((*s) + i) & (RTSIZE-1)];
	s++;
}
return i;
}
Match_node * add_to_right_table_list(Match_node * m, Match_node * l) {
if (l==NULL) return m;
if ((m->d->right->word) <= (l->d->right->word)) {
	m->next = l;
	return m;
} else {
	l->next = add_to_right_table_list(m, l->next);
	return l;
}
}
Match_node * add_to_left_table_list(Match_node * m, Match_node * l) {
if (l==NULL) return m;
if ((m->d->left->word) >= (l->d->left->word)) {
	m->next = l;
	return m;
} else {
	l->next = add_to_left_table_list(m, l->next);
	return l;
}
}
void put_into_match_table(int size, Match_node ** t,
			  Disjunct * d, Connector * c, int dir ) {
int h;
Match_node * m;
h = fast_match_hash(c) & (size-1);
m = (Match_node *) xalloc (sizeof(Match_node));
m->next = NULL;
m->d = d;
if (dir == 1) {
	t[h] = add_to_right_table_list(m, t[h]);
} else {
	t[h] = add_to_left_table_list(m, t[h]);
}
}
void init_fast_matcher() {
int w, len, size, i;
Match_node ** t;
Disjunct * d;
match_cost = 0;
for (w=0; w<N_words; w++) {
	len = left_disjunct_list_length(sentence[w].d);
	size = next_power_of_two_up(len);
	l_table_size[w] = size;
	t = l_table[w] = (Match_node **) xalloc(size * sizeof(Match_node *));
	for (i=0; i<size; i++) t[i] = NULL;
	for (d=sentence[w].d; d!=NULL; d=d->next) {
	    if (d->left != NULL) {
		put_into_match_table(size, t, d, d->left, -1);
	    }
	}
	len = right_disjunct_list_length(sentence[w].d);
	size = next_power_of_two_up(len);
	r_table_size[w] = size;
	t = r_table[w] = (Match_node **) xalloc(size * sizeof(Match_node *));
	for (i=0; i<size; i++) t[i] = NULL;
	for (d=sentence[w].d; d!=NULL; d=d->next) {
	    if (d->right != NULL) {
		put_into_match_table(size, t, d, d->right, 1);
	    }
	}
}
}
Match_node * form_match_list
(int w, Connector *lc, int lw, Connector *rc, int rw) {
Match_node *ml, *mr, *mx, *my, * mz, *front, *free_later;
if (lc!=NULL) {
	ml = l_table[w][fast_match_hash(lc) & (l_table_size[w]-1)];
} else {
	ml = NULL;
}
if (rc!=NULL) {
	mr = r_table[w][fast_match_hash(rc) & (r_table_size[w]-1)];
} else {
	mr = NULL;
}
front = NULL;
for (mx = ml; mx!=NULL; mx=mx->next) {
	if (mx->d->left->word < lw) break;
	my = get_match_node();
	my->d = mx->d;
	my->next = front;
	front = my;
}
ml = front;
front = NULL;
for (mx = mr; mx!=NULL; mx=mx->next) {
	if (mx->d->right->word > rw) break;
	my = get_match_node();
	my->d = mx->d;
	my->next = front;
	front = my;
}
mr = front;
free_later = NULL;
front = NULL;
for(mx = mr; mx != NULL; mx=mz) {
	
	mz = mx->next;
	match_cost++;
	for (my=ml; my!=NULL; my=my->next) {
	    match_cost++;
	    if (mx->d == my->d) break;
	}
	if (my != NULL) {
	    mx->next = free_later;
	    free_later = mx;
	}
	if (my==NULL) {
	    mx->next = front;
	    front = mx;
	}
}
mr = front;
put_match_list(free_later);
if (mr == NULL) return ml;
for (mx = mr; mx->next != NULL; mx = mx->next)
;
mx->next = ml;
return mr;
}
/* 当前文件是D:\Read\idiom.c*/

int contains_underbar(char * s) {
while(*s != '\0') {
	if (*s == '_') return TRUE;
	s++;
}
return FALSE;
}
int is_idiom_string(char * s) {
char * t;
for (t=s; *t != '\0'; t++) {
	if (*t == '.') {
	    return FALSE;
	}
}
if ((s[0] == '_') || (s[strlen(s)-1] == '_')) {
	return FALSE;
}
for (t=s; *t != '\0'; t++) {
	if ((*t == '_') && (*(t+1) == '_')) {
	    return FALSE;
	}
}
return TRUE;
}
int is_number(char *s) {
while(*s != '\0') {
	if (!isdigit(*s)) return FALSE;
	s++;
}
return TRUE;
}
int numberfy(char * s) {
for (; (*s != '\0') && (*s != '.'); s++)
;
if (*s++ != '.') return -1;
if (*s++ != 'I') return -1;
if (!is_number(s)) return -1;
return atoi(s);
}
int max_postfix_found(Dict_node * d) {
int i, j;
i = 0;
while(d != NULL) {
	j = numberfy(d->string);
	if (j > i) i = j;
	d = d->right;
}
return i;
}
char * build_idiom_word_name(char * s) {
char * new_s, * x;
int count;
count = max_postfix_found(dictionary_lookup(s))+1;
new_s = x = (char *) xalloc(strlen(s) + 10);
while((*s != '\0') && (*s != '.')) {
	*x = *s;
	x++;
	s++;
}
sprintf(x,".I%d",count);
return new_s;
}
Dict_node * make_idiom_Dict_nodes(char * s) {
Dict_node * dn, * dn_new;
char * t;
int more;
dn = NULL;
while (*s != '\0') {
	t = s;
	while((*s != '\0') && (*s != '_')) s++;
	if (*s == '_') {
	    more = TRUE;
	    *s = '\0';
	} else {
	    more = FALSE;
	}
	dn_new = (Dict_node *) xalloc(sizeof (Dict_node));
	dn_new->right = dn;
	dn = dn_new;
	dn->string = t;
	dn->file = NULL;
	if (more) s++;
}
return dn;
}
static char current_name[] = "AAAAAAAA";
#define CN_size (sizeof(current_name)-1)
void increment_current_name(void) {
int i, carry;
i = CN_size-1;
carry = 1;
while (carry == 1) {
	current_name[i]++;
	if (current_name[i] == 'Z'+1) {
	    current_name[i] = 'A';
	    carry = 1;
	} else {
	    carry = 0;
	}
	i--;
}
}
char * generate_id_connector(void) {
unsigned int i;
char * t, * s;
for (i=0; current_name[i] == 'A'; i++)
;
s = t = (char *) xalloc(CN_size - i + 2 + 1 + 1);
*t++ = 'I';
*t++ = 'D';
for (; i < CN_size; i++ ) {
	*t++ = current_name[i] ;
}
*t++ = '\0';
return s;
}
void insert_idiom(Dict_node * dn) {
Exp * nc, * no, * n1;
E_list *ell, *elr;
char * s;
int s_length;
Dict_node * dn_list, * xdn, * start_dn_list;
no = dn->exp;
s = dn->string;
s_length = strlen(s);
if (!is_idiom_string(s)) {
	printf("*** Word \"%s\" on line %d is not",s, line_number);
	printf(" a correctly formed idiom string.\n");
	printf("    This word will be ignored\n");
	xfree((char *)s, s_length+1);
	xfree((char *)dn, sizeof (Dict_node));
	return;
}
dn_list = start_dn_list = make_idiom_Dict_nodes(s);
xfree((char *)dn, sizeof (Dict_node));
if (dn_list->right == NULL) {
error("Idiom string with only one connector -- should have been caught");
}
nc = (Exp *) xalloc(sizeof(Exp));
nc->u.string = generate_id_connector();
nc->dir = '-';
nc->multi = FALSE;
nc->type = CONNECTOR_type;
nc->cost = 0;
n1 = (Exp *) xalloc(sizeof(Exp));
n1->u.l = ell = (E_list *) xalloc(sizeof(E_list));
ell->next = elr = (E_list *) xalloc(sizeof(E_list));
elr->next = NULL;
ell->e = nc;
elr->e = no;
n1->type = AND_type;
n1->cost = 0;
dn_list->exp = n1;
dn_list = dn_list->right;
while(dn_list->right != NULL) {
	
	
	n1 = (Exp *) xalloc(sizeof(Exp));
	n1->u.string = NULL;
	n1->type = AND_type;
	n1->cost = 0;
	n1->u.l = ell = (E_list *) xalloc(sizeof(E_list));
	ell->next = elr = (E_list *) xalloc(sizeof(E_list));
	elr->next = NULL;
	
	nc = (Exp *) xalloc(sizeof(Exp));
	nc->u.string = generate_id_connector();
	nc->dir = '+';
	nc->multi = FALSE;
	nc->type = CONNECTOR_type;
	nc->cost = 0;
	elr->e = nc;
	
	increment_current_name();
	
	nc = (Exp *) xalloc(sizeof(Exp));
	nc->u.string = generate_id_connector();
	nc->dir = '-';
	nc->multi = FALSE;
	nc->type = CONNECTOR_type;
	nc->cost = 0;
	ell->e = nc;
	
	dn_list->exp = n1;
	
	dn_list = dn_list->right;
}
nc = (Exp *) xalloc(sizeof(Exp));
nc->u.l = ell = (E_list *) xalloc(sizeof(E_list));
ell->next = elr = (E_list *) xalloc(sizeof(E_list));
elr->next = NULL;
ell->e = elr->e = NULL;
nc->u.string = generate_id_connector();
nc->dir = '+';
nc->multi = FALSE;
nc->type = CONNECTOR_type;
nc->cost = 0;
dn_list->exp = nc;
increment_current_name();
dn_list = start_dn_list;
while (dn_list != NULL) {
	xdn = dn_list->right;
	dn_list->left = dn_list->right = NULL;
dn_list->string = build_idiom_word_name(dn_list->string);
	dict_root = insert_dict(dict_root, dn_list);
	N_dict++;
	dn_list = xdn;
}
xfree((char *)s, s_length+1);
}
int is_idiom_word(char * s) {
return (numberfy(s) != -1) ;
}
/* 当前文件是D:\Read\massage.c*/

#define COMMA_LABEL   (-2)
#define EITHER_LABEL  (-3)
#define NEITHER_LABEL (-4)
#define NOT_LABEL     (-5)
#define NOTONLY_LABEL (-6)
#define BOTH_LABEL    (-7)
Disjunct * glom_comma_connector(Disjunct * d) {
Disjunct * d_list, * d1, * d2;
Connector * c, * c1;
d_list = NULL;
for (d1 = d; d1!=NULL; d1=d1->next) {
	if (d1->left == NULL) continue;
	for (c = d1->left; c->next != NULL; c = c->next)
	  ;
	if (c->label < 0) continue;
	d2 = copy_disjunct(d1);
	d2->next = d_list;
	d_list = d2;
	c1 = (Connector *) xalloc(sizeof(Connector));
	c1->string="";
	c1->label = COMMA_LABEL;
	c1->priority = THIN_priority;
	c1->multi=FALSE;	
	c1->next = NULL;
	c->next = c1;
}
return catenate_disjuncts(d, d_list);
}
Disjunct * glom_aux_connector(Disjunct * d, int label, int necessary) {
Disjunct * d_list, * d1, * d2;
Connector * c, * c1, *c2;
d_list = NULL;
for (d1 = d; d1!=NULL; d1=d1->next) {
	if (d1->left == NULL) continue;
	for (c = d1->left; c->next != NULL; c = c->next)
	  ;
	if (c->label < 0) continue;
	if (!necessary) {
	    d2 = copy_disjunct(d1);
	    d2->next = d_list;
	    d_list = d2;
	}
	c1 = (Connector *) xalloc(sizeof(Connector));
	c1->string="";
	c1->label = label;
	c1->priority = THIN_priority;
	c1->multi=FALSE;
	c1->next = c;
	if (d1->left == c) {
	    d1->left = c1;
	} else {
	    for (c2 = d1->left; c2->next != c; c2 = c2->next)
	      ;
	    c2->next = c1;
	}
}
return catenate_disjuncts(d, d_list);
}
Disjunct * add_one_connector(int label, int dir, char *cs, Disjunct * d) {
Connector * c;
c = (Connector *) xalloc(sizeof(Connector));
c->string= cs;
c->label = label;
c->priority = THIN_priority;
c->multi=FALSE;
c->next = NULL;
if (dir == '+') {
	c->next = d->right;
	d->right = c;
} else {
	c->next = d->left;
	d->left = c;
}
return d;
}
Disjunct * special_disjunct(int label, int dir, char *cs, char * ds) {
Disjunct * d1;
Connector * c;
d1 = (Disjunct *) xalloc(sizeof(Disjunct));
d1->cost = 0;
d1->string = ds;
d1->next = NULL;
c = (Connector *) xalloc(sizeof(Connector));
c->string= cs;
c->label = label;
c->priority = THIN_priority;
c->multi=FALSE;
c->next = NULL;
if (dir == '+') {
	d1->left = NULL;
	d1->right = c;
} else {
	d1->right = NULL;
	d1->left = c;
}
return d1;
}
void construct_comma(void) {
int w;
for (w=0; w<N_words-1; w++) {
	if ((strcmp(sentence[w].string, ",")==0) &&
	            is_conjunction[w+1]) {
	    sentence[w].d = catenate_disjuncts(
		   special_disjunct(COMMA_LABEL,'+',"", ","),
		   sentence[w].d);
	    sentence[w+1].d = glom_comma_connector(sentence[w+1].d);
	}
}
}
void construct_either(void) {
int w;
if (!sentence_contains("either")) return;
for (w=0; w<N_words; w++) {
	if (strcmp(sentence[w].string, "either") != 0) continue;
	sentence[w].d = catenate_disjuncts(
special_disjunct(EITHER_LABEL,'+',"", "either"),
sentence[w].d);
}
for (w=0; w<N_words; w++) {
	if (strcmp(sentence[w].string, "or") != 0) continue;
	sentence[w].d = glom_aux_connector
	                  (sentence[w].d, EITHER_LABEL, FALSE);
}
}
void construct_neither(void) {
int w;
if (!sentence_contains("neither")) {
	for (w=0; w<N_words; w++) {
	    if (strcmp(sentence[w].string, "nor") != 0) continue;
	    free_disjuncts(sentence[w].d);
	    sentence[w].d = NULL;
	}
	return;
}
for (w=0; w<N_words; w++) {
	if (strcmp(sentence[w].string, "neither") != 0) continue;
	sentence[w].d = catenate_disjuncts(
		   special_disjunct(NEITHER_LABEL,'+',"", "neither"),
		   sentence[w].d);
}
for (w=0; w<N_words; w++) {
	if (strcmp(sentence[w].string, "nor") != 0) continue;
	sentence[w].d = glom_aux_connector
	                  (sentence[w].d, NEITHER_LABEL, TRUE);
}
}
void construct_notonlybut(void) {
int w;
Disjunct *d;
if (!sentence_contains("not")) {
	return;
}
for (w=0; w<N_words; w++) {
	if (strcmp(sentence[w].string, "not") != 0) continue;
	sentence[w].d = catenate_disjuncts(
	     special_disjunct(NOT_LABEL,'+',"", "not"),
	     sentence[w].d);
	if (w<N_words-1 &&  strcmp(sentence[w+1].string, "only")==0) {
	    sentence[w+1].d = catenate_disjuncts(
special_disjunct(NOTONLY_LABEL, '-',"","only"),
sentence[w+1].d);
	    d = special_disjunct(NOTONLY_LABEL, '+', "","not");
	    d = add_one_connector(NOT_LABEL,'+',"", d);
	    sentence[w].d = catenate_disjuncts(d, sentence[w].d);
	}
}
for (w=0; w<N_words; w++) {
	if (strcmp(sentence[w].string, "but") != 0) continue;
	sentence[w].d = glom_aux_connector
	                  (sentence[w].d, NOT_LABEL, TRUE);
}
}
void construct_both(void) {
int w;
if (!sentence_contains("both")) return;
for (w=0; w<N_words; w++) {
	if (strcmp(sentence[w].string, "both") != 0) continue;
	sentence[w].d = catenate_disjuncts(
special_disjunct(BOTH_LABEL,'+',"", "both"),
sentence[w].d);
}
for (w=0; w<N_words; w++) {
	if (strcmp(sentence[w].string, "and") != 0) continue;
	sentence[w].d = glom_aux_connector
	                  (sentence[w].d, BOTH_LABEL, FALSE);
}
}
/* 当前文件是D:\Read\parse.c*/

#define INFINITY 1000
#define NO_ISLANDS TRUE
int match(Connector *a, Connector *b) {
char *s, *t;
int x, y;
if (a->label != b->label) return FALSE;
x = a->priority;
y = b->priority;
s = a->string;
t = b->string;
while(isupper(*s) || isupper(*t)) {
	if (*s != *t) return FALSE;
	s++;
	t++;
}
if ((x==THIN_priority) && (y==THIN_priority)) {
	
	while ((*s!='\0') && (*t!='\0')) {
	    if ((*s == '*') || (*t == '*') ||
		((*s == *t) && (*s != '^'))) {
		s++;
		t++;
	    } else return FALSE;
	}
	return TRUE;
} else if ((x==UP_priority) && (y==DOWN_priority)) {
	
	while ((*s!='\0') && (*t!='\0')) {
	    if ((*s == *t) || (*s == '*') || (*t == '^')) {
		s++;
		t++;
	    } else return FALSE;
	}
	return TRUE;
} else if ((y==UP_priority) && (x==DOWN_priority)) {
	while ((*s!='\0') && (*t!='\0')) {
	    if ((*s == *t) || (*t == '*') || (*s == '^')) {
		s++;
		t++;
	    } else return FALSE;
	}
	return TRUE;
} else return FALSE;
}
typedef struct Table_connector Table_connector;
struct Table_connector {
short              lw, rw;
Connector         *le, *re;
short              cost;
int                count;
Table_connector   *next;
};
static int table_size;
static Table_connector ** table;
void init_table(void) {
int i;
if (N_words >= 10) {
	table_size = (1<<16);
	
} else if (N_words >= 4) {
	table_size = (1 << (((6*(N_words-4))/6) + 4));
} else {
	table_size = (1 << 4);
}
table = (Table_connector**) xalloc(table_size * sizeof(Table_connector*));
for (i=0; i<table_size; i++) {
	table[i] = NULL;
}
}
int hash(int lw, int rw, Connector *le, Connector *re, int cost) {
int i;
i = 0;
i = i + (i<<1) + randtable[(lw + i) & (RTSIZE - 1)];
i = i + (i<<1) + randtable[(rw + i) & (RTSIZE - 1)];
i = i + (i<<1) + randtable[(((long) le + i) % (table_size+1)) & (RTSIZE - 1)];
i = i + (i<<1) + randtable[(((long) re + i) % (table_size+1)) & (RTSIZE - 1)];
i = i + (i<<1) + randtable[(cost+i) & (RTSIZE - 1)];
return i & (table_size-1);
}
void free_table(void) {
int i;
Table_connector *t, *x;
for (i=0; i<table_size; i++) {
	for(t = table[i]; t!= NULL; t=x) {
	    x = t->next;
	    xfree((void *) t, sizeof(Table_connector));
	}
}
xfree((void *) table, table_size * sizeof(Table_connector*));
}
Table_connector * table_pointer(int lw, int rw, Connector *le, Connector *re, int cost) {
Table_connector *t;
N_hash_lookups++;
work_in_hash_lookups++;
t = table[hash(lw, rw, le, re, cost)];
for (; t != NULL; t = t->next) {
	work_in_hash_lookups++;
	if ((t->lw == lw) && (t->rw == rw) && (t->le == le) && (t->re == re) && (t->cost == cost))  return t;
}
return NULL;
}
int table_lookup(int lw, int rw, Connector *le, Connector *re, int cost) {
Table_connector *t = table_pointer(lw, rw, le, re, cost);
if (t == NULL) return -1; else return t->count;
}
Table_connector * table_store(int lw, int rw, Connector *le, Connector *re, int cost, int count){
Table_connector *t, *n;
int h;
N_in_table++;
n = (Table_connector *) xalloc(sizeof(Table_connector));
n->count = count;
n->lw = lw; n->rw = rw; n->le = le; n->re = re; n->cost = cost;
h = hash(lw, rw, le, re, cost);
t = table[h];
n->next = t;
table[h] = n;
return n;
}
void table_update(int lw, int rw, Connector *le, Connector *re, int cost, int count) {
Table_connector *t = table_pointer(lw, rw, le, re, cost);
assert(t != NULL, "This entry is supposed to be in the table.");
t->count = count;
}
int pseudocount(int lw, int rw, Connector *le, Connector *re, int cost) {
int count;
count = table_lookup(lw, rw, le, re, cost);
if (count == 0) return 0; else return 1;
}
int count(int lw, int rw, Connector *le, Connector *re, int cost) {
Disjunct * d;
int total, pseudototal;
int start_word, end_word, w;
int leftcount, rightcount;
int lcost, rcost, Lmatch, Rmatch;
Match_node * m, *m1;
Table_connector *t;
if (cost < 0) return 0;
t = table_pointer(lw, rw, le, re, cost);
if (t == NULL) {
	t = table_store(lw, rw, le, re, cost, 0);
	
} else {
	return t->count;
}
if (rw == 1+lw) {
	
	
	if ((le == NULL) && (re == NULL) && (cost == 0)) {
	    t->count = 1;
	} else {
	    t->count = 0;
	}
	return t->count;
}
if ((le == NULL) && (re == NULL)) {
#if NO_ISLANDS
	
	if (cost == rw-lw-1) {
	    t->count = 1;
	} else {
	    t->count = 0;
	}
	return t->count;
#else
	if (cost == 0) {
	
	
	
	    t->count = 0;
	} else {
	    total = 0;
	    w = lw+1;
	    for (d = sentence[w].d; d != NULL; d = d->next) {
		if (d->left == NULL) {
		    total += count(w, rw, d->right, NULL, cost-1);
		}
	    }
	    total += count(w, rw, NULL, NULL, cost-1);
	    t->count = total;
	}
	return t->count;
#endif	
}
if (le == NULL) {
	start_word = lw+1;
} else {
	start_word = le->word;
}
if (re == NULL) {
	end_word = MIN(rw-1, lw+maxlinklength);
} else {
	end_word = re->word;
}
total = 0;
for (w=start_word; w <= end_word; w++) {
	m1 = m = form_match_list(w, le, lw, re, rw);
	for (; m!=NULL; m=m->next) {
	    d = m->d;
	    for (lcost = 0; lcost <= cost; lcost++) {
		rcost = cost-lcost;
		
		
		Lmatch = (le != NULL) && (d->left != NULL) && match(le, d->left);
		Rmatch = (d->right != NULL) && (re != NULL) && match(d->right, re);
		rightcount = leftcount = 0;
		if (Lmatch) {
		    leftcount = pseudocount(lw, w, le->next, d->left->next, lcost);
		    if (le->multi) leftcount += pseudocount(lw, w, le, d->left->next, lcost);
		    if (d->left->multi) leftcount += pseudocount(lw, w, le->next, d->left, lcost);
		    if (le->multi && d->left->multi) leftcount += pseudocount(lw, w, le, d->left, lcost);
		}
		
		if (Rmatch) {
		    rightcount = pseudocount(w, rw, d->right->next, re->next, rcost);
		    if (d->right->multi) rightcount += pseudocount(w,rw,d->right,re->next, rcost);
		    if (re->multi) rightcount += pseudocount(w, rw, d->right->next, re, rcost);
		    if (d->right->multi && re->multi) rightcount += pseudocount(w, rw, d->right, re, rcost);
		}
		pseudototal = leftcount*rightcount;
		if (leftcount > 0) {
		
		    pseudototal += leftcount * pseudocount(w, rw, d->right, re, rcost);
		}
		if ((le == NULL) && (rightcount > 0)) {
		
		    pseudototal += rightcount * pseudocount(lw, w, le, d->left, lcost);
		}
		
		if (pseudototal != 0) {
		    rightcount = leftcount = 0;
		    if (Lmatch) {
			leftcount = count(lw, w, le->next, d->left->next, lcost);
			if (le->multi) leftcount += count(lw, w, le, d->left->next, lcost);
			if (d->left->multi) leftcount += count(lw, w, le->next, d->left, lcost);
			if (le->multi && d->left->multi) leftcount += count(lw, w, le, d->left, lcost);
		    }
		    if (Rmatch) {
			rightcount = count(w, rw, d->right->next, re->next, rcost);
			if (d->right->multi) rightcount += count(w,rw,d->right,re->next, rcost);
			if (re->multi) rightcount += count(w, rw, d->right->next, re, rcost);
			if (d->right->multi && re->multi) rightcount += count(w, rw, d->right, re, rcost);
		    }
		    total += leftcount*rightcount;
		    if (leftcount > 0) {
			
			total += leftcount * count(w, rw, d->right, re, rcost);
		    }
		    if ((le == NULL) && (rightcount > 0)) {
			
			total += rightcount * count(lw, w, le, d->left, lcost);
		    }
		}
	    }
	}
	
	put_match_list(m1);
}
t->count = total;
return total;
}
int parse(int cost) {
Disjunct * dis;
int total=0;
for (dis = sentence[0].d; dis != NULL; dis = dis->next) {
	if (dis->left == NULL) {
	    total += count(0, N_words, dis->right, NULL, cost);
	}
}
total += count(0, N_words, NULL, NULL, cost);
if (verbosity > 1) {
	printf("Total count with cost %d:   %d\n", cost, total);
}
return total;
}
int region_valid(int lw, int rw, Connector *le, Connector *re) {
Disjunct * d;
int left_valid, right_valid, found;
int i, start_word, end_word;
int w;
Match_node * m, *m1;
i = table_lookup(lw, rw, le, re, 0);
if (i >= 0) return i;
if ((le == NULL) && (re == NULL) && deletable[lw][rw]) {
	table_store(lw, rw, le, re, 0, 1);
	return 1;
}
if (le == NULL) {
	start_word = lw+1;
} else {
	start_word = le->word;
}
if (re == NULL) {
	end_word = MIN(rw-1, lw+maxlinklength);
} else {
	end_word = re->word;
}
found = 0;
for (w=start_word; w <= end_word; w++) {
	m1 = m = form_match_list(w, le, lw, re, rw);
	for (; m!=NULL; m=m->next) {
	    d = m->d;
	    mark_cost++;
	
	    left_valid = (((le != NULL) && (d->left != NULL) && prune_match(le, d->left)) &&
			  ((region_valid(lw, w, le->next, d->left->next)) ||
			   ((le->multi) && region_valid(lw, w, le, d->left->next)) ||
			   ((d->left->multi) && region_valid(lw, w, le->next, d->left)) ||
			   ((le->multi && d->left->multi) && region_valid(lw, w, le, d->left))));
	    if (left_valid && region_valid(w, rw, d->right, re)) {
		found = 1;
		break;
	    }
	    right_valid = (((d->right != NULL) && (re != NULL) && prune_match(d->right, re)) &&
			   ((region_valid(w, rw, d->right->next,re->next))    ||
			    ((d->right->multi) && region_valid(w,rw,d->right,re->next))  ||
			    ((re->multi) && region_valid(w, rw, d->right->next, re))  ||
			    ((d->right->multi && re->multi) && region_valid(w, rw, d->right, re))));
	    if ((left_valid && right_valid) || (right_valid && region_valid(lw, w, le, d->left))) {
		found = 1;
		break;
	    }
	}
	put_match_list(m1);
	if (found != 0) break;
}
table_store(lw, rw, le, re, 0, found);
return found;
}
void mark_region(int lw, int rw, Connector *le, Connector *re) {
Disjunct * d;
int left_valid, right_valid, i;
int start_word, end_word;
int w;
Match_node * m, *m1;
i = region_valid(lw, rw, le, re);
if ((i==0) || (i==2)) return;
table_update(lw, rw, le, re, 0, 2);
if ((le == NULL) && (re == NULL) && (null_links) && (rw != 1+lw)) {
	w = lw+1;
	for (d = sentence[w].d; d != NULL; d = d->next) {
	    if ((d->left == NULL) && region_valid(w, rw, d->right, NULL)) {
		d->marked = TRUE;
		mark_region(w, rw, d->right, NULL);
	    }
	}
	mark_region(w, rw, NULL, NULL);
	return;
}
if (le == NULL) {
	start_word = lw+1;
} else {
	start_word = le->word;
}
if (re == NULL) {
	end_word = MIN(rw-1, lw+maxlinklength);
} else {
	end_word = re->word;
}
for (w=start_word; w <= end_word; w++) {
	m1 = m = form_match_list(w, le, lw, re, rw);
	for (; m!=NULL; m=m->next) {
	    d = m->d;
	    mark_cost++;
	    left_valid = (((le != NULL) && (d->left != NULL) && prune_match(le, d->left)) &&
			  ((region_valid(lw, w, le->next, d->left->next)) ||
			   ((le->multi) && region_valid(lw, w, le, d->left->next)) ||
			   ((d->left->multi) && region_valid(lw, w, le->next, d->left)) ||
			   ((le->multi && d->left->multi) && region_valid(lw, w, le, d->left))));
	    right_valid = (((d->right != NULL) && (re != NULL) && prune_match(d->right, re)) &&
			   ((region_valid(w, rw, d->right->next,re->next)) ||
			    ((d->right->multi) && region_valid(w,rw,d->right,re->next))  ||
			    ((re->multi) && region_valid(w, rw, d->right->next, re)) ||
			    ((d->right->multi && re->multi) && region_valid(w, rw, d->right, re))));
	
	
	
	    if (left_valid && region_valid(w, rw, d->right, re)) {
		d->marked = TRUE;
		mark_region(w, rw, d->right, re);
		mark_region(lw, w, le->next, d->left->next);
		if (le->multi) mark_region(lw, w, le, d->left->next);
		if (d->left->multi) mark_region(lw, w, le->next, d->left);
		if (le->multi && d->left->multi) mark_region(lw, w, le, d->left);
	    }
	
	    if (right_valid && region_valid(lw, w, le, d->left)) {
		d->marked = TRUE;
		mark_region(lw, w, le, d->left);
		mark_region(w, rw, d->right->next,re->next);
		if (d->right->multi) mark_region(w,rw,d->right,re->next);
		if (re->multi) mark_region(w, rw, d->right->next, re);
		if (d->right->multi && re->multi) mark_region(w, rw, d->right, re);
	    }
	
	    if (left_valid && right_valid) {
		d->marked = TRUE;
		mark_region(lw, w, le->next, d->left->next);
		if (le->multi) mark_region(lw, w, le, d->left->next);
		if (d->left->multi) mark_region(lw, w, le->next, d->left);
		if (le->multi && d->left->multi) mark_region(lw, w, le, d->left);
		mark_region(w, rw, d->right->next,re->next);
		if (d->right->multi) mark_region(w,rw,d->right,re->next);
		if (re->multi) mark_region(w, rw, d->right->next, re);
		if (d->right->multi && re->multi) mark_region(w, rw, d->right, re);
	    }
	}
	put_match_list(m1);
}
}
void conjunction_prune(void) {
Disjunct * d, * d_head, * dx;
int w;
for (w=0; w<N_words; w++) {
	for (d=sentence[w].d; d != NULL; d=d->next) {
	    d->marked = FALSE;
	}
}
init_fast_matcher();
init_table();
for (d = sentence[0].d; d != NULL; d = d->next) {
	if ((d->left == NULL) && region_valid(0, N_words, d->right, NULL)) {
	    mark_region(0, N_words, d->right, NULL);
	    d->marked = TRUE;
	}
}
for (w=0; w<N_words; w++) {
	d_head = NULL;
	for (d=sentence[w].d; d != NULL; d=dx) {
	    dx = d->next;
	    if (d->marked) {
		d->next = d_head;
		d_head = d;
	    } else {
		d->next = NULL;
		free_disjuncts(d);
	    }
	}
	sentence[w].d = d_head;
}
free_fast_matcher();
free_table();
}
/* 当前文件是D:\Read\post-process.c*/

static char * domain_starter_links[] =
{"W", "Ce", "Cs", "Ca", "Cc", "Ci", "R*", "Re", "RSe",
		"Mr", "QI#d", "Mv", "Jr", "Mj", "Qd",
"TOn", "TOi", "Mg", "MVi",
"Ss#d", "Bsd", "ER", "Z",
"Ma", "SIs#g",
		"BIqx", "MX#p", "MX#a", "MX#r", "MX#j", "MV#o", "MV#p",
		"Eq", "COq", "CP", "AFd", "PFc",
		NULL};
static char * urfl_domain_starter_links[] = {"TOo", "I#j",
"Pa##j", NULL};
static char * urfl_only_domain_starter_links[] = {"SFsx", "Ss#g",
"COp", NULL};
typedef struct connector_domain_name_pair_struct CDNP;
struct connector_domain_name_pair_struct {char * string; int n;};
CDNP CDNP_array[] = {{"Ce", 'e'}, {"R", 'r'}, {"Re", 'r'}, {"W", 'm'},
		       {"RSe", 'e'}, {"Cs", 's'}, {"Ca", 's'},  {"Jr", 'e'},
		       {"Mr", 'r'}, {"Cc", 's'},
{"Mv", 'e'}, {"QI#d", 's'}, {"BIqx", 's'},
		       {"TOn", 'e'}, {"TOi", 'e'},
{"MVi", 'e'}, {"MV#o", 's'}, {"MV#p", 's'},
		       {"AFd", 's'}, {"PFc", 's'},
		       {"Mg", 'e'}, {"Mj", 'j'}, {"Qd", 'm'},
		       {"MX#j", 'j'}, {"TOo", 'x'}, {"I#j", 'x'},
		       {"Pa##j", 'x'}, {"COp", 'd'},
		       {"SFsx", 'd'}, {"Ss#g", 'd'}, {"SIs#g", 's'},
		       {"Ss#d", 's'},
{"Bsd", 's'}, {"ER", 's'}, {"Z", 's'},
{"Ma", 'e'}, {"MX#p", 'e'}, {"Ci", 'e'}, {"MX#a", 'e'},
		       {"Eq", 'e'}, {"COq", 'e'}, {"CP", 'd'},
		       {"MX#r", 'r'},
		       {NULL, 0}};
static char * domain_contains_links[] = {"Mg", "Mx", "Bsd",
"MX#a", "Ma", "Mv", "MX#r",
"Ss#d", "CP", "Ws", "Wq", "Qd", "Mj", "Wj", "Wi",
"MX#j", "AFd", "PFc", "Jr", "Wd", NULL};
static char * ignore_these_links[] = {"Xca", NULL};
static char * must_be_connected_without[] = {"R*",
"Re", "TOt", "EXx", "HA",  "SFsic", "Jr", NULL};
static char * restricted_links[] = {"B#*",
"D##w", "B#w", "B#d", "AFh",
"MVt", "Xx", "HL", "SFsic", "AFd", "Bc", "CX", "CP",
"EAh", "H", "HA", "PFc", "B#j", "Wd", "PF", "Z", NULL};
int ppmatch(char *s, char *t) {
char c;
while(isupper(*s) || isupper(*t)) {
	if (*s != *t) return FALSE;
	s++;
	t++;
}
while (*s != '\0') {
	if (*s != '#') {
	    if (*t == '\0') c = '*'; else c = *t;
	    if (*s != c) return FALSE;
	}
	s++;
	t++;
}
return TRUE;
}
int find_domain_name(char * string) {
int i;
for (i=0; CDNP_array[i].string != NULL; i++) {
	if (ppmatch(CDNP_array[i].string, string)) {
	    return CDNP_array[i].n;
	}
}
return 0;
}
typedef struct d_tree_leaf_struct D_tree_leaf;
typedef struct domain_struct Domain;
struct domain_struct{
char * string;
int size;
List_o_links * lol;
int start_link;
int type;
D_tree_leaf * child;
Domain * parent;
};
struct d_tree_leaf_struct{
Domain * parent;
int link;
D_tree_leaf * next;
};
static Domain domain_array[MAX_LINKS];
static int N_domains;
static int N_domain_trees;
static List_o_links * word_links[MAX_SENTENCE];
void print_domain(int d) {
List_o_links * lol;
for (lol=domain_array[d].lol; lol != NULL; lol = lol->next) {
	print_a_link(stdout, lol->link);
}
printf("\n");
}
void print_domains(void) {
int d;
for (d=0; d<N_domains; d++)  {
	printf("domain %d \"%s\"\n", d, domain_array[d].string);
	print_domain(d);
}
}
int post_process_match(char * s, char * t) {
while(isupper(*s) || isupper(*t)) {
	if (*s != *t) return FALSE;
	s++;
	t++;
}
while ((*s!='\0') && (*t!='\0')) {
	if ((*s == '*') || (*t == '*') ||
	    ((*s == *t) && (*s != '^'))) {
	    s++;
	    t++;
	} else return FALSE;
}
return TRUE;
}
int match_in_list(char * s, char * a[]) {
int i;
for (i=0; a[i] != NULL; i++) {
	if (post_process_match(s,a[i])) {
	    return TRUE;
	}
}
return FALSE;
}
int string_in_list(char * s, char * a[]) {
int i;
for (i=0; a[i] != NULL; i++) {
	if (ppmatch(a[i], s)) {
	    return TRUE;
	}
}
return FALSE;
}
void build_graph(void) {
int i, link;
List_o_links * lol;
for (i=0; i<N_words; i++) {
	word_links[i] = NULL;
}
for (link=0; link<N_links; link++) {
	if (pp_link_array[link].l == -1) continue;
	if (string_in_list(pp_link_array[link].name, ignore_these_links)) {
	    continue;
	}
	lol = (List_o_links *) xalloc(sizeof(List_o_links));
	lol->next = word_links[pp_link_array[link].l];
	word_links[pp_link_array[link].l] = lol;
	lol->link = link;
	lol->word = pp_link_array[link].r;
	lol = (List_o_links *) xalloc(sizeof(List_o_links));
	lol->next = word_links[pp_link_array[link].r];
	word_links[pp_link_array[link].r] = lol;
	lol->link = link;
	lol->word = pp_link_array[link].l;
}
}
void add_link_to_domain(int link) {
List_o_links *lol;
lol = (List_o_links *) xalloc(sizeof(List_o_links));
lol->next = domain_array[N_domains].lol;
domain_array[N_domains].lol = lol;
domain_array[N_domains].size++;
lol->link = link;
}
static int visited[MAX_SENTENCE];
void depth_first_search(int w, int root, int start_link) {
List_o_links * lol;
visited[w] = TRUE;
for (lol = word_links[w]; lol != NULL; lol = lol->next) {
	if (lol->word < w && lol->link != start_link) {
	    add_link_to_domain(lol->link);
	}
}
for (lol = word_links[w]; lol != NULL; lol = lol->next) {
	if (!visited[lol->word] && (lol->word != root) &&
	    !(lol->word < root && lol->word < w &&
	    string_in_list(pp_link_array[lol->link].name, restricted_links))) {
	    depth_first_search(lol->word, root, start_link);
	}
}
}
void bad_depth_first_search(int w, int root, int start_link) {
List_o_links * lol;
visited[w] = TRUE;
for (lol = word_links[w]; lol != NULL; lol = lol->next) {
	if ((lol->word < w)  && (lol->link != start_link) && (w != root)) {
	    add_link_to_domain(lol->link);
	}
}
for (lol = word_links[w]; lol != NULL; lol = lol->next) {
	if ((!visited[lol->word]) && !(w == root && lol->word < w) &&
	    !(lol->word < root && lol->word < w &&
	    string_in_list(pp_link_array[lol->link].name, restricted_links))) {
	    bad_depth_first_search(lol->word, root, start_link);
	}
}
}
void d_depth_first_search(int w, int root, int right, int start_link) {
List_o_links * lol;
visited[w] = TRUE;
for (lol = word_links[w]; lol != NULL; lol = lol->next) {
	if ((lol->word < w) && (lol->link != start_link) && (w != root)) {
	    add_link_to_domain(lol->link);
	}
}
for (lol = word_links[w]; lol != NULL; lol = lol->next) {
	if (!visited[lol->word] && !(w == root && lol->word >= right) &&
!(w == root && lol->word < root) &&
	    !(lol->word < root && lol->word < w &&
	    string_in_list(pp_link_array[lol->link].name, restricted_links))) {
	    d_depth_first_search(lol->word, root, right, start_link);
	}
}
}
int domain_compare(Domain * d1, Domain * d2) {
return (d1->size - d2->size) ;
}
void build_domains(void) {
int link, i, d;
char * s;
N_domains = 0;
for (link = 0; link<N_links; link++) {
	if (pp_link_array[link].l == -1) continue;
	if (string_in_list(pp_link_array[link].name, ignore_these_links)) {
	    continue;
	}
	s = pp_link_array[link].name;
	if (string_in_list(s, domain_starter_links)) {
	    for (i=0; i<N_words; i++) {
		visited[i] = FALSE;
	    }
	    domain_array[N_domains].string = s;
	    domain_array[N_domains].lol = NULL;
	    domain_array[N_domains].size = 0;
	    domain_array[N_domains].start_link = link;
	    if (string_in_list(s, domain_contains_links)) {
		add_link_to_domain(link);
	    }
	    depth_first_search(pp_link_array[link].r, pp_link_array[link].l, link);
	    N_domains++;
	} else if (string_in_list(s, urfl_domain_starter_links)) {
	    for (i=0; i<N_words; i++) {
		visited[i] = FALSE;
	    }
	    domain_array[N_domains].string = s;
	    domain_array[N_domains].lol = NULL;
	    domain_array[N_domains].size = 0;
	    domain_array[N_domains].start_link = link;
	    add_link_to_domain(link);
	    bad_depth_first_search(pp_link_array[link].r,pp_link_array[link].l,link);
	    N_domains++;
	} else if (string_in_list(s, urfl_only_domain_starter_links)) {
	    for (i=0; i<N_words; i++) {
		visited[i] = FALSE;
	    }
	    domain_array[N_domains].string = s;
	    domain_array[N_domains].lol = NULL;
	    domain_array[N_domains].size = 0;
	    domain_array[N_domains].start_link = link;
	    d_depth_first_search(
	       pp_link_array[link].l,pp_link_array[link].l,pp_link_array[link].r,link);
	    N_domains++;
	}
}
qsort((void *)domain_array, N_domains, sizeof(Domain),
	  (int (*)(const void *, const void *))domain_compare);
for (d=0; d<N_domains; d++) {
	i = find_domain_name(domain_array[d].string);
	if (i==0) {
	    printf("something wrong with domain name %s\n",
		    domain_array[d].string);
	    exit(1);
	}
	domain_array[d].type = i;
}
}
int contained_in(Domain * d1, Domain * d2) {
char mark[MAX_LINKS];
List_o_links * lol;
int i;
for (i=0; i<N_links; i++) {
	mark[i] = FALSE;
}
for (lol=d2->lol; lol != NULL; lol = lol->next) {
	mark[lol->link] = TRUE;
}
for (lol=d1->lol; lol != NULL; lol = lol->next) {
	if (!mark[lol->link]) return FALSE;
}
return TRUE;
}
int link_in_domain(int link, Domain * d) {
List_o_links * lol;
for (lol = d->lol; lol != NULL; lol = lol->next) {
	if (lol->link == link) return TRUE;
}
return FALSE;
}
int check_domain_nesting() {
Domain * d1, * d2;
int counts[4];
char mark[MAX_LINKS];
List_o_links * lol;
int i;
for (d1=domain_array; d1 < domain_array + N_domains; d1++) {
	for (d2=d1+1; d2 < domain_array + N_domains; d2++) {
	    for (i=0; i<N_links; i++) {
		mark[i] = 0;
	    }
	    for (lol=d2->lol; lol != NULL; lol = lol->next) {
		mark[lol->link] = 1;
	    }
	    for (lol=d1->lol; lol != NULL; lol = lol->next) {
		mark[lol->link] += 2;
	    }
	    counts[0] = counts[1] = counts[2] = counts[3] = 0;
	    for (i=0; i<N_links; i++) counts[(int) mark[i]]++;
	    if ((counts[1] > 0) && (counts[2] > 0) && (counts[3] > 0)) {
		return FALSE;
	    }
	}
}
return TRUE;
}
void build_domain_forest() {
int d, d1, link;
D_tree_leaf * dtl;
if (N_domains > 0) {
	domain_array[N_domains-1].parent = NULL;
}
N_domain_trees = 1;
for (d=0; d < N_domains-1; d++) {
	for (d1 = d+1; d1 < N_domains; d1++) {
	    if (contained_in(&domain_array[d], &domain_array[d1])) {
		domain_array[d].parent = &domain_array[d1];
		break;
	    }
	}
	if (d1 == N_domains) {
	    domain_array[d].parent = NULL;
	    N_domain_trees++;
	
	}
}
for (d=0; d < N_domains; d++) {
	domain_array[d].child = NULL;
}
for (link=0; link < N_links; link++) {
	if (pp_link_array[link].l == -1) continue;
	for (d=0; d<N_domains; d++) {
	    if (link_in_domain(link, &domain_array[d])) {
		dtl = (D_tree_leaf *) xalloc(sizeof(D_tree_leaf));
		dtl->link = link;
		dtl->parent = &domain_array[d];
		dtl->next = domain_array[d].child;
		domain_array[d].child = dtl;
		break;
	    }
	}
}
}
void free_list_o_links(List_o_links *lol) {
List_o_links * xlol;
while(lol != NULL) {
	xlol = lol->next;
	xfree((char *)lol, sizeof(List_o_links));
	lol = xlol;
}
}
void free_D_tree_leaves(D_tree_leaf *dtl) {
D_tree_leaf * xdtl;
while(dtl != NULL) {
	xdtl = dtl->next;
	xfree((char *)dtl, sizeof(D_tree_leaf));
	dtl = xdtl;
}
}
void free_post_processing_structures(void) {
int w, d;
for (w=0; w<N_words; w++) {
	free_list_o_links(word_links[w]);
}
for (d=0; d<N_domains; d++) {
	free_list_o_links(domain_array[d].lol);
	free_D_tree_leaves(domain_array[d].child);
}
}
void print_domain_tree() {
int d;
D_tree_leaf * dtl;
printf("Domain     It's parent \n");
for (d=0; d<N_domains-1; d++) {
	printf(" %3d        %3d\n", d, (int) (domain_array[d].parent - domain_array));
}
for (d=0; d<N_domains; d++) {
	printf("Link children of domain %d:\n", d);
	for (dtl=domain_array[d].child; dtl != NULL; dtl = dtl->next) {
	    print_a_link(stdout, dtl->link);
	}
}
}
int CCG_rule() {
int d, t;
for (d=0; d<N_domains; d++) {
	if ((domain_array[d].type == 'c') && (domain_array[d].parent!=NULL)) {
	    t = domain_array[d].parent->type;
	    if ((t != 'g') && (t != 'c')) return FALSE;
	}
}
return TRUE;
}
int domain_bounded(int d_type) {
int d, lw;
List_o_links * lol;
for (d=0; d<N_domains; d++) {
	if (domain_array[d].type != d_type) continue;
	lw = pp_link_array[domain_array[d].start_link].l;
	for (lol = domain_array[d].lol; lol != NULL; lol = lol->next) {
	    if (pp_link_array[lol->link].l < lw) return FALSE;
	}
}
return TRUE;
}
int link_inhabits(char * link_name, int d_type){
int d;
D_tree_leaf * c;
for (d=0; d<N_domains; d++) {
	for (c = domain_array[d].child; c != NULL; c = c->next) {
	    if (ppmatch(link_name, pp_link_array[c->link].name)) {
		if (domain_array[d].type != d_type) return FALSE;
	    }
	}
}
return TRUE;
}
int group_type_contains(int d_type, char * link_name) {
int d;
D_tree_leaf * c;
for (d=0; d<N_domains; d++) {
	if (domain_array[d].type != d_type) continue;
	for (c=domain_array[d].child; c != NULL; c = c->next) {
	    if (ppmatch(link_name, pp_link_array[c->link].name)) break;
	}
	if (c == NULL) return FALSE;
}
return TRUE;
}
int group_type_contains_all(int d_type, char * name_list[]) {
int i;
for (i=0; name_list[i] != NULL; i++) {
	if (!group_type_contains(d_type, name_list[i])) return FALSE;
}
return TRUE;
}
int group_type_contains_one(int d_type, char * name_list[]) {
int d, i;
int count;
D_tree_leaf * c;
for (d=0; d<N_domains; d++) {
	if (domain_array[d].type != d_type) continue;
	count = 0;
	for (i=0; name_list[i] != NULL; i++) {
	    for (c=domain_array[d].child; c != NULL; c = c->next) {
		if (ppmatch(name_list[i], pp_link_array[c->link].name)) count++;
	    }
	}
	if (count != 1) return FALSE;
}
return TRUE;
}
int contains_none(char * selector, char * incompat[]) {
D_tree_leaf * dtl;
int d;
for (d=0; d<N_domains; d++) {
	for (dtl = domain_array[d].child; dtl != NULL; dtl = dtl->next) {
	    if (ppmatch(selector, pp_link_array[dtl->link].name)) break;
	}
	if (dtl != NULL) {
	    for (dtl = domain_array[d].child; dtl != NULL; dtl = dtl->next) {
		if (string_in_list(pp_link_array[dtl->link].name, incompat)) {
		    return FALSE;
		}
	    }
	}
}
return TRUE;
}
int ordering_constraint(char * X, char * Y) {
D_tree_leaf * dtl;
int d, leftmost_y, rightmost_x;
for (d=0; d<N_domains; d++) {
	leftmost_y = N_words;
rightmost_x = -1;
	for (dtl = domain_array[d].child; dtl != NULL; dtl = dtl->next) {
	    if ((strcmp(pp_link_array[dtl->link].name, Y) == 0)) {
		if (leftmost_y > pp_link_array[dtl->link].r) {
		    leftmost_y = pp_link_array[dtl->link].r;
		}
	    } else if ((strcmp(pp_link_array[dtl->link].name, X) == 0)) {
		if (rightmost_x < pp_link_array[dtl->link].r) {
		    rightmost_x = pp_link_array[dtl->link].r;
		}
	    }
	}
	if (leftmost_y <= rightmost_x) return FALSE;
}
return TRUE;
}
int contains_one(char * selector, char * required[]) {
D_tree_leaf * dtl;
int d, count;
for (d=0; d<N_domains; d++) {
	for (dtl = domain_array[d].child; dtl != NULL; dtl = dtl->next) {
	    if (ppmatch(selector, pp_link_array[dtl->link].name)) break;
	}
	if (dtl != NULL) {
	    count = 0;
	    for (dtl = domain_array[d].child; dtl != NULL; dtl = dtl->next) {
		if (string_in_list(pp_link_array[dtl->link].name, required)) {
		    count++;
		}
	    }
	    if (count < 1) return FALSE;
	}
}
return TRUE;
}
void connectivity_dfs(int w, char * s[]){
List_o_links *lol;
visited[w] = TRUE;
for (lol = word_links[w]; lol != NULL; lol = lol->next) {
	if (!visited[lol->word] &&
	    !string_in_list(pp_link_array[lol->link].name, s)) {
	    connectivity_dfs(lol->word, s);
	}
}
}
void mark_reachable_words(int w){
List_o_links *lol;
if (visited[w]) return;
visited[w] = TRUE;
for (lol = word_links[w]; lol != NULL; lol = lol->next) {
	mark_reachable_words(lol->word);
}
}
int is_connected_without(char * s[]) {
int i;
for (i=0; i<N_words; i++) {
	visited[i] = FALSE;
}
mark_reachable_words(0);
for (i=0; i<N_words; i++) {
	visited[i] = !visited[i];
}
connectivity_dfs(0, s);
for (i=0; i<N_words; i++) {
	if (visited[i] == FALSE) {
	    return FALSE;
	}
}
return TRUE;
}
int is_connected(void) {
int i;
for (i=0; i<N_words; i++) visited[i] = (word_links[i] == NULL);
mark_reachable_words(0);
for (i=0; i<N_words; i++) if (!visited[i]) return FALSE;
return TRUE;
}
static char * incompat_with_THi[] =  {"I*", "PP*", "TO*", "Pa*", "Pam",
	  "S", "SI", "Pg*", "Pv*", "LE*", "AFd*", "MVta",
	  NULL};
static char * SFiSFIi[] =  {"SFsi", "SFIsi", "OXi", NULL};
static char * Necessary_for_SF[] =  {"TOi", "THi", "QIi",
"TSi", "O#i", "Ci", "THb", "COqi", "CPi", "Eqi", "AFdi", NULL};
static char * Necessary_for_MVt[] = {"Dm#m", "EAm", "EEm", "MVm",
	  "Pam", "Pafm", "AFm", "EB#m", "MVb", "Om", "Mam",
	  "Am", "Jm", "Ds*m", NULL};
static char * Nec_for_MVz[] = {"D##y", "EAy", "EEy", "MVy",
	  "EB#y", NULL};
static char * Opt[] = {"Opt", "Omt", "O*t", "Bp#t", "B*#t", "Bc#t",
	  NULL};
static char * Ost[] = {"O*t", "Ost", "Omt", "Bs#t", "B*#t", "Bc#t",
NULL};
static char * Oxt[] = {"O#t", "B##t", NULL};
static char * Nec_for_BIh[] = {"Ss#b", "SIs#b", NULL};
static char * Nec_for_THb[] = {"S##t", "SI##t",
	      "SFsi", "SFIsi", NULL};
static char * Nec_for_BIq[] = {"S##q", "SI##q", "SFsi",
"Ss#b", "SFIsi", "SIs#b", NULL};
static char * Necessary_for_Thcom[] = {"TH", NULL};
static char * Necessary_for_Tvcom[] = {"TOi*", NULL};
static char * Necessary_for_Tocom[] = {"TO**", "TOf*", NULL};
static char * Necessary_for_Tvcom_Trans[] = {"TOt*", NULL};
static char * MVm[] = {"MVm", NULL};
static char * MV[] = {"MVa", "MVp", NULL};
static char * EBmm[] = {"EB#m", "EB#y", NULL};
static char * Pa_or_Paf[] = {"Pa*", "Paf*", NULL};
static char * Nec_for_MVto[] = {"D##m", "D##y", "Om", "Oy", "Jm", "Jy",
	      "Am", NULL};
static char * Nec_for_MVtp[] = {"EEm", "MVb", "Dm#m", "EEy", "D##y",
"MVm", "Om", "Oy", "Jm", "Jy", "Am", NULL};
static char * Nec_for_MVta[] = {"Pam", "Pafm", "EAm", "Ds*m", "EAy", "AFm", "Mam", "Am", NULL};
static char * Nec_for_Cc[] = {"EEm", "EEy", "MVm", "MVb", "MVy", NULL};
static char * Nec_for_Mc[] = {"Dm#m", NULL};
static char * Nec_for_Sp_com[] = {"Dmcm", "Dmcy", "Om", "Oy",
"Jm", "Jy", NULL};
static char * Nec_for_Ss_com[] = {"Dmum", "Dmuy", "Om", "Oy",
"Jm", "Jy", "Ds*y", NULL};
static char * Nec_for_S_com[] = {"Dm#m", "D##y", "Om",
"Oy", "Jm", "Jy", NULL};
static char * Nec_for_Inv[] = {"Wq", "Qd", "CQ", "PFc", NULL};
static char * Incompat_with_Ws[] =
{"B#m", "Ca", "BT", NULL};
static char * Nec_for_Ws_2[] = {"D##w", "S##w", "H", NULL};
static char * Nec_for_Wq[] = {"SI", "SFI", NULL};
static char * Nec_for_Ma[] = {"TO", "TOf", "TH", "MVp", "TOt", "QI", "OF",
"MVt", "MVz", "MVh", "Ytm", "Ya", NULL};
static char * Nec_for_Ia[] = {"B#m", "B#w", NULL};
static char * Jr[] = {"Jr", NULL};
static char * Nec_for_Jr[] = {"B#j", NULL};
static char * Nec_for_j[] = {"JQ", "Jw", NULL};
static char * Mj_or_Wj[] = {"Mj", "Wj", "MX#j", NULL};
static char * Nec_for_Qe[] = {"EEh", NULL};
static char * Nec_for_EAh[] = {"AF", "Bsm", "B*m", "Qe", "Ca", "AFm",
NULL};
static char * ZZ[] = {"ZZ", NULL};
static char * Nec_for_MVh[] = {"EExk", "EAxk", "D##k",
NULL};
static char * Incompat_with_MXsr[] = {"Sp#w", NULL};
static char * Incompat_with_MXpr[] = {"Ss#w", "S#iw", NULL};
static char * illegal_S_types[] = {"Spxi", "Spi*", "Spit",
"Spiq", "Spib", "Spiw", NULL};
static char * illegal_SI_types[] = {"SIpxi", "SIpi*", "SIpit",
"SIpiq", "SIpib", NULL};
void free_PP_node(PP_node * p) {
D_type_list * dtl, * dtlx;
Violation_list * v, *vx;
int i;
for (i=0; i<N_links; i++){
	for (dtl = p->d_type_array[i]; dtl != NULL; dtl = dtlx) {
	    dtlx = dtl->next;
	    xfree((char *) dtl, sizeof(D_type_list));
	}
}
if (N_links > 0) xfree((char *) p->d_type_array, N_links * sizeof(D_type_list *));
for (v = p->v; v!=NULL; v = vx) {
	vx = v->next;
	xfree((char *) v, sizeof(Violation_list));
}
xfree((char *) p, sizeof (PP_node));
}
D_type_list ** build_type_array(void) {
D_type_list ** array, * dtl;
int d, i;
List_o_links * lol;
array = NULL;
if (N_links > 0) array = (D_type_list **) xalloc(N_links * sizeof(D_type_list *));
for (i=0; i<N_links; i++) {
	array[i] = NULL;
}
for (d=0; d<N_domains; d++) {
	for (lol=domain_array[d].lol; lol != NULL; lol = lol->next) {
	    dtl = (D_type_list *) xalloc(sizeof(D_type_list));
	    dtl->next = array[lol->link];
	    array[lol->link] = dtl;
	    dtl->type = domain_array[d].type;
	}
}
return array;
}
PP_node * bogus_pp_node(void) {
PP_node * pp_return;
int link;
pp_return = (PP_node *) xalloc(sizeof(PP_node));
pp_return->d_type_array =
(D_type_list **) xalloc(N_links * sizeof(D_type_list *));
for (link=0; link<N_links; link++) {
	pp_return->d_type_array[link] = NULL;
}
pp_return->v = NULL;
return pp_return;
}
Violation_list * issue_violation(Violation_list * v, char * string) {
Violation_list * v1;
v1 = (Violation_list *) xalloc(sizeof (Violation_list));
v1->string = string;
v1->next = v;
return v1;
}
#define PP(condition,message) {                                 \
if ((condition)) {                                          \
	v = issue_violation(v, (message));                      \
	goto done_checking;                                     \
}                                                           \
}
PP_node * post_process(void){
Violation_list * v;
PP_node * pp_return;
if(!postprocess_defined) return bogus_pp_node();
pp_return = (PP_node *) xalloc(sizeof(PP_node));
build_graph();
build_domains();
build_domain_forest();
v = NULL;
#if ! defined FOR_RELEASE
if(!check_domain_nesting()) {
	if (display_bad) {
	    printf("FYI: The domains are not nested.\n");
	}
}
#endif
PP(!is_connected_without(must_be_connected_without),
"Connectivity violation");
PP(!is_connected(), "Connectivity violation");
PP(!domain_bounded('s'), "Unbounded s domain");
PP(!domain_bounded('r'), "Unbounded r domain");
PP(!contains_one("SI#*", Nec_for_Inv),    "question inversion violated");
PP(!contains_one("SI#i", Nec_for_Inv),    "question inversion violated");
PP(!contains_one("SI#x", Nec_for_Inv),  "question inversion violated");
PP(!contains_one("SFI##*", Nec_for_Inv), "question inversion violated");
PP(!contains_none("Ws", Incompat_with_Ws), "question inversion violated");
PP(!contains_one("Ws", Nec_for_Ws_2),   "question inversion violated");
PP(!contains_one("I#a", Nec_for_Ia),"incorrect use of 'to'");
PP(!contains_one("Wq", Nec_for_Wq),"question inversion violated");
PP(!contains_one("Qd", Nec_for_Wq),"question inversion violated");
PP(!contains_one("PFc", Nec_for_Wq),"question inversion violated");
PP(!contains_one("Mj", Nec_for_j),"misuse of question word");
PP(!contains_one("MX#j", Nec_for_j),"misuse of question word");
PP(!contains_one("Wj", Nec_for_j),"misuse of question word");
PP(!contains_one("JQ", Mj_or_Wj),"misuse of preposition");
PP(!contains_one("Jw", Mj_or_Wj),"misuse of preposition");
PP(!contains_one("B#j", Jr),"A B*j must have a Jr");
PP(!contains_one("Jr", Nec_for_Jr),"A Jr must have an B*j");
PP(!contains_one("EAh", Nec_for_EAh),"Incorrect use of 'how'");
PP(!contains_one("EEh", Nec_for_EAh),"Incorrect use of 'how'");
PP(!contains_one("Qe", Nec_for_Qe), "Incorrect use of adverb");
PP(!contains_one("THi", SFiSFIi),"THi rule 1 violated");
PP(!contains_one("TSi", SFiSFIi),"TSi rule 1 violated");
PP(!contains_one("QIi", SFiSFIi),"QIi rule 1 violated");
PP(!contains_one("TOi", SFiSFIi),"TV rule 1 violated");
PP(!contains_one("Ci", SFiSFIi),"Ci rule 1 violated");
PP(!contains_one("COqi", SFiSFIi),"It rules violated");
PP(!contains_one("CPi", SFiSFIi),"It rules violated");
PP(!contains_one("Eqi", SFiSFIi),"It rules violated");
PP(!contains_one("LEi", SFiSFIi),"THi rule 1 violated");
PP(!contains_one("MVti", SFiSFIi),"THi rule 1 violated");
PP(!contains_one("AFdi", SFiSFIi),"THi rule 1 violated");
PP(!contains_one("O#i", SFiSFIi),"O#i rule 1 violated");
PP(!contains_none("SF", incompat_with_THi),"There rule 1 violated");
PP(!contains_none("SFI", incompat_with_THi),"There rule 1 violated");
PP(!contains_none("OX", incompat_with_THi),"OXt rule 1 violated");
PP(!contains_one("SFst", Ost),"There rule 2 violated");
PP(!contains_one("SFIst", Ost),"There rule 2 violated");
PP(!contains_one("SFp", Opt),"There rule 2 violated");
PP(!contains_one("SFIp", Opt),"There rule 2 violated");
PP(!contains_one("OXt", Oxt),"There rule 2 violated");
PP(!contains_one("SFsi*", Necessary_for_SF),"It rule violated");
PP(!contains_one("SFIsi", Necessary_for_SF),"It rule violated");
PP(!contains_one("THb", Nec_for_THb),"be-that rule violated");
PP(!contains_one("BIh", Nec_for_BIh),"be-complement rule violated");
PP(!contains_one("BIq", Nec_for_BIq),"be-complement rule violated");
PP(!contains_one("OXi", Necessary_for_SF),"SF rule violated");
PP(!contains_one("MVt", Necessary_for_MVt),"Than rule violated");
PP(!contains_one("MVz", Nec_for_MVz),"As rule violated");
PP(!contains_one("MV#a", Nec_for_MVta),"bad use of comparative");
PP(!contains_one("MV#i", Nec_for_MVta),"bad use of comparative");
PP(!contains_one("MV#o", Nec_for_MVto),"bad use of comparative");
PP(!contains_one("MV#p", Nec_for_MVtp),"bad use of comparative");
PP(!contains_one("Pafc", EBmm),"Than-adj 1 violated");
PP(!contains_one("Pafc", Pa_or_Paf),"Than-adj 2 violated");
PP(!contains_one("MVat", MVm),"Than-adv 1 violated");
PP(!contains_one("MVpt", MVm),"Than-prep 1 violated");
PP(!contains_one("MVat", MV),"Than-adv 2 violated");
PP(!contains_one("MVpt", MV),"Than-prep 2 violated");
PP(!contains_one("U#t", Nec_for_MVto),"Than-obj 2 violated");
PP(!contains_one("Cc", Nec_for_Cc),"Cc violated");
PP(!contains_one("Mc", Nec_for_Mc),"Mc violated");
PP(!contains_one("Sp#c", Nec_for_Sp_com),"Sp_com violated");
PP(!contains_one("Ss#c", Nec_for_Ss_com),"Ss_com violated");
PP(!contains_one("S*ic", Nec_for_Ss_com),"Ss_com violated");
PP(!contains_one("S##c", Nec_for_S_com),"S_com violated");
PP(!contains_one("THc", Necessary_for_Thcom),"That-comparative rule violated");
PP(!contains_one("TOfc", Necessary_for_Tocom),"To-comparative rule violated");
PP(!contains_one("TOic", Necessary_for_Tvcom),"To-comparative rule violated");
PP(!contains_one("TOtc", Necessary_for_Tvcom_Trans),"To-comparative rule violated");
PP(!contains_one("Ma*", Nec_for_Ma), "bad use of adjective");
PP(!contains_one("Mam", Nec_for_Ma), "bad use of adjective");
PP(!contains_one("MX#a", Nec_for_Ma), "bad use of adjective");
PP(!contains_one("Ixd", ZZ),"Can't use \"do\" with that verb");
PP(!contains_one("Oxn", ZZ),"Can't use a tag word after a pronoun");
PP(!contains_none("S", illegal_S_types),"bad n-v agreement");
PP(!contains_none("SI", illegal_SI_types),"bad n-v agreement");
PP(!contains_one("MVh", Nec_for_MVh),"Incorrect use of that");
PP(!contains_none("MXsr", Incompat_with_MXsr),"Bad n-v agreement");
PP(!contains_none("MXpr", Incompat_with_MXpr),"Bad n-v agreement");
done_checking:
pp_return->d_type_array = build_type_array();
pp_return->v = v;
free_post_processing_structures();
return pp_return;
}
/* 当前文件是D:\Read\print.c*/

/*static int center[MAX_SENTENCE];
char * chosen_words[MAX_SENTENCE];
static int N_words_to_print;*/
void set_centers(int print_word_0) {
int i, len, tot;
tot = 0;
if (print_word_0) i=0; else i=1;
for (; i<N_words_to_print; i++) {
	len = strlen(chosen_words[i]);
	center[i] = tot + (len/2);
	tot += len+1;
}
}
static int link_heights[MAX_LINKS];
static int row_starts[MAX_SENTENCE];
static int N_rows;
void print_postscript_data(FILE *fp, int print_word_0, int print_word_N) {
int link, i,j;
int d;
if (print_word_0) d=0; else d=1;
i = 0;
fprintf(fp,"[");
for (j=d; j<N_words_to_print; j++) {
	if ((i%7 == 0) && (i>0)) fprintf(fp,"\n");
	i++;
	fprintf(fp,"(%s)",chosen_words[j]);
}
fprintf(fp,"]");
fprintf(fp,"\n");
fprintf(fp,"[");
j = 0;
for (link=0; link<N_links; link++) {
	if (!print_word_0 && (pp_link_array[link].l == 0)) continue;
	if (!print_word_N && (pp_link_array[link].r == N_words-1)) continue;
	if (pp_link_array[link].l == -1) continue;
	if ((j%5 == 0) && (j>0)) fprintf(fp,"\n");
	j++;
	fprintf(fp,"[%d %d %d",
		pp_link_array[link].l-d, pp_link_array[link].r-d, link_heights[link]);
	if (pp_link_array[link].lc->label < 0) {
	    fprintf(fp," (%s)]", pp_link_array[link].name);
	} else {
	    fprintf(fp," ()]");
	}
}
fprintf(fp,"]");
fprintf(fp,"\n");
fprintf(fp,"[");
for (j=0; j<N_rows; j++ ){
	fprintf(fp,"%d ", row_starts[j]);
}
fprintf(fp,"]\n");
}
void compute_chosen_words(void) {
int i, l;
char * s, *t, *u;
for (i=0; i<N_words; i++) {
	chosen_words[i] = sentence[i].string;
	if (chosen_disjuncts[i] == NULL) {
	    t = chosen_words[i];
	    l = strlen(t) + 2;
	    s = (char *) xalloc(l+1);
	    sprintf(s, "[%s]", t);
	    free_this_string_later(s, l+1);
	    chosen_words[i] = s;
	} else if (display_word_subscripts) {
	    t = chosen_disjuncts[i]->string;	
	    if (is_idiom_word(t)) {
		l = strlen(t);
		s = (char *) xalloc(l+1);
		free_this_string_later(s, l+1);
		strcpy(s,t);
		for (u=s; *u != '.'; u++)
		  ;
		*u = '\0';
		chosen_words[i] = s;
	    } else {
		chosen_words[i] = t;
	    }
	}
}
if (left_wall_defined) {
	chosen_words[0] = LEFT_WALL_DISPLAY;
}
if (right_wall_defined) {
	chosen_words[N_words-1] = RIGHT_WALL_DISPLAY;
}
}
#define MAX_HEIGHT 30
static char picture[MAX_HEIGHT][MAX_LINE];
static char xpicture[MAX_HEIGHT][MAX_LINE];
void print_links_graphically(FILE *fp) {
int i, j, k, cl, cr, row, top_row, width, flag;
char *t, *s;
int print_word_0 = 0, print_word_N = 0, N_wall_connectors, suppressor_used;
char connector[MAX_TOKEN_LENGTH];
int line_len, link_length;
N_wall_connectors = 0;
if (left_wall_defined) {
	suppressor_used = FALSE;
	for (j=0; j<N_links; j++) {
	    if (pp_link_array[j].l == 0) {
		N_wall_connectors ++;
		if (strcmp(pp_link_array[j].lc->string, LEFT_WALL_SUPPRESS)==0){
		    suppressor_used = TRUE;
		}
	    }
	}
	print_word_0 = (!suppressor_used) || (N_wall_connectors > 1) || display_walls;
} else {
	print_word_0 = TRUE;
}
N_wall_connectors = 0;
if (right_wall_defined) {
	suppressor_used = FALSE;
	for (j=0; j<N_links; j++) {
	    if (pp_link_array[j].r == N_words-1) {
		N_wall_connectors ++;
		if (strcmp(pp_link_array[j].lc->string, RIGHT_WALL_SUPPRESS)==0){
		    suppressor_used = TRUE;
		}
	    }
	}
	print_word_N = (!suppressor_used) || (N_wall_connectors > 1) || display_walls;
} else {
	print_word_N = TRUE;
}
N_words_to_print = N_words;
if (!print_word_N) N_words_to_print--;
set_centers(print_word_0);
line_len = center[N_words_to_print-1]+1;
for (k=0; k<MAX_HEIGHT; k++) {
	for (j=0; j<line_len; j++) picture[k][j] = ' ';
	picture[k][line_len] = '\0';
}
top_row = 0;
for (link_length = 1; link_length < N_words_to_print; link_length++) {
	for (j=0; j<N_links; j++) {
	    if (pp_link_array[j].l == -1) continue;
	    if ((pp_link_array[j].r - pp_link_array[j].l) != link_length)
	      continue;
	    if (!print_word_0 && (pp_link_array[j].l == 0)) continue;
	
	    if (!print_word_N && (pp_link_array[j].r == N_words-1)) continue;	
	
	
	    cl = center[pp_link_array[j].l];
	    cr = center[pp_link_array[j].r];
	    for (row=0; row < MAX_HEIGHT; row++) {
		for (k=cl+1; k<cr; k++) {
		    if (picture[row][k] != ' ') break;
		}
		if (k == cr) break;
	    }
	
	    link_heights[j] = row;
	
	    if (2*row+2 > MAX_HEIGHT-1) {
		fprintf(fp,"The diagram is too high.\n");
		return;
	    }
	    if (row > top_row) top_row = row;
	
	    picture[row][cl] = '+';
	    picture[row][cr] = '+';
	    for (k=cl+1; k<cr; k++) {
		picture[row][k] = '-';
	    }
	
	    s = pp_link_array[j].name;
	
	    if (display_link_subscripts) {
	      if (!isalpha(*s))
		s = "";
	    } else {
	      if (!isupper(*s)) {
		s = "";
	      }
	    }
	    strncpy(connector, s, MAX_TOKEN_LENGTH-1);
	    connector[MAX_TOKEN_LENGTH-1] = '\0';
	    k=0;
	    if (display_link_subscripts)
	      k = strlen(connector);
	    else
	      for (t=connector; isupper(*t); t++) k++;
	    if ((cl+cr-k)/2 + 1 <= cl) {
		t = picture[row] + cl + 1;
	    } else {
		t = picture[row] + (cl+cr-k)/2 + 1;
	    }
	    s = connector;
	    if (display_link_subscripts)
	      while((*s != '\0') && (*t == '-')) *t++ = *s++;
	    else
	      while(isupper(*s) && (*t == '-')) *t++ = *s++;
	
	    for (k=0; k<row; k++) {
		if (picture[k][cl] == ' ') {
		    picture[k][cl] = '|';
		}
		if (picture[k][cr] == ' ') {
		    picture[k][cr] = '|';
		}
	    }
	}
}
s = xpicture[0];
if (print_word_0) k = 0; else k = 1;
for (; k<N_words_to_print; k++) {
	t = chosen_words[k];
	i=0;
	while(*t != '\0') {
	    *s++ = *t++;
	    i++;
	}
	*s++ = ' ';
}
*s = '\0';
if (display_short) {
	for (k=0; picture[0][k] != '\0'; k++) {
	    if ((picture[0][k] == '+') || (picture[0][k] == '|')) {
		xpicture[1][k] = '|';
	    } else {
		xpicture[1][k] = ' ';
	    }
	}
	xpicture[1][k] = '\0';
	for (row=0; row <= top_row; row++) {
	    strcpy(xpicture[row+2],picture[row]);
	}
	top_row = top_row+2;
} else {
	for (row=0; row <= top_row; row++) {
	    strcpy(xpicture[2*row+2],picture[row]);
	    for (k=0; picture[row][k] != '\0'; k++) {
		if ((picture[row][k] == '+') || (picture[row][k] == '|')) {
		    xpicture[2*row+1][k] = '|';
		} else {
		    xpicture[2*row+1][k] = ' ';
		}
	    }
	    xpicture[2*row+1][k] = '\0';
	}
	top_row = 2*top_row + 2;
}
if (print_word_0) i = 0; else i = 1;
k = 0;
N_rows = 0;
row_starts[N_rows] = 0;
N_rows++;
while(i < N_words_to_print) {
	putc('\n',fp);
	width = 0;
	do {
	    width += strlen(chosen_words[i])+1;
	    i++;
	} while((i<N_words_to_print) &&
	      (width + ((int) strlen(chosen_words[i]))+1 < screen_width));
	row_starts[N_rows] = i - (!print_word_0);
	if (i<N_words_to_print) N_rows++;
	for (row = top_row; row >= 0; row--) {
	    flag = TRUE;
	    for (j=k;flag&&(j<k+width)&&(xpicture[row][j]!='\0'); j++){
		flag = flag && (xpicture[row][j] == ' ');
	    }
	    if (!flag) {
		for (j=k;(j<k+width)&&(xpicture[row][j]!='\0'); j++){
		    putc(xpicture[row][j], fp);
		}
		putc('\n', fp);
	    }
	}
	putc('\n', fp);
	k += width;
}
if (display_postscript) print_postscript_data(fp, print_word_0, print_word_N);
}
void print_disjunct_counts(void) {
int i;
int c;
Disjunct *d;
for (i=0; i<N_words; i++) {
	c = 0;
	for (d=sentence[i].d; d != NULL; d = d->next) {
	    c++;
	}
	printf("%s(%d) ",sentence[i].string, c);
}
printf("\n\n");
}
void print_expression_sizes(void) {
X_node * x;
int w, size;
for (w=0; w<N_words; w++) {
	size = 0;
	for (x=sentence[w].x; x!=NULL; x = x->next) {
	    size += size_of_expression(x->exp);
	}
	printf("%s[%d] ",sentence[w].string, size);
}
printf("\n\n");
}
void print_sentence(FILE *fp, int w) {
int i;
if (left_wall_defined) i=1; else i=0;
if (w == 0) i+=w;
for (; i<N_words - right_wall_defined; i++) {
	fprintf(fp, "%s ", sentence[i].string);
}
fprintf(fp, "\n");
}
/* 当前文件是D:\Read\prune.c*/

int prune_match(Connector *a, Connector *b) {
char *s, *t;
int x, y;
if (a->label != b->label) return FALSE;
x = a->priority;
y = b->priority;
s = a->string;
t = b->string;
while(isupper(*s) || isupper(*t)) {
	if (*s != *t) return FALSE;
	s++;
	t++;
}
if ((x==THIN_priority) && (y==THIN_priority)) {
#if defined PLURALIZATION	
	if ((*(a->string)=='S') && ((*s=='s') || (*s=='p')) &&
	    ((*t=='p') || (*t=='s')) &&
	    ((s-1 == a->string) || ((s-2 == a->string) && (*(s-1) == 'I')))){
	    return TRUE;
	}
#endif	
	while ((*s!='\0') && (*t!='\0')) {
	    if ((*s == '*') || (*t == '*') ||
		((*s == *t) && (*s != '^'))) {
		s++;
		t++;
	    } else return FALSE;
	}
	return TRUE;
} else if ((x==UP_priority) && (y==DOWN_priority)) {
	while ((*s!='\0') && (*t!='\0')) {
	    if ((*s == *t) || (*s == '*') || (*t == '^')) {
		s++;
		t++;
	    } else return FALSE;
	}
	return TRUE;
} else if ((y==UP_priority) && (x==DOWN_priority)) {
	while ((*s!='\0') && (*t!='\0')) {
	    if ((*s == *t) || (*t == '*') || (*s == '^')) {
		s++;
		t++;
	    } else return FALSE;
	}
	return TRUE;
} else return FALSE;
}
static int s_table_size;
static Connector ** table1;
void free_S(void) {
int i;
for (i=0; i<s_table_size; i++) {
	if (table1[i] == NULL) continue;
	free_connectors(table1[i]);
	table1[i] = NULL;
}
}
int hash_S(Connector * c) {
char *s;
int i;
i = c->label;
s = c->string;
while(isupper(*s)) {
	i = i + (i<<1) + randtable[(*s + i) & (RTSIZE-1)];
	s++;
}
return (i & (s_table_size-1));
}
void insert_S(Connector * c) {
int h;
Connector * e;
h = hash_S(c);
for (e = table1[h]; e != NULL; e = e->next) {
	if ((strcmp(c->string, e->string) == 0) &&
	    (c->label == e->label) && (c->priority == e->priority)) {
	    return;
	}
}
e = (Connector *) xalloc(sizeof(Connector)) ;
*e = *c;
e->next = table1[h];
table1[h] = e;
}
void zero_S(void) {
int i;
for (i=0; i<s_table_size; i++) {
	table1[i] = NULL;
}
}
void init_S(Connector * c) {
int h;
Connector *c1;
for (; c!=NULL; c = c->next) {
	h = hash_S(c);
	c1 = (Connector *) xalloc(sizeof(Connector)) ;
	*c1 = *c;
	c1->next = table1[h];
	table1[h] = c1;
}
}
int matches_S(Connector * c, int dir) {
int h;
Connector * e;
h = hash_S(c);
if (dir=='-') {
	for (e = table1[h]; e != NULL; e = e->next) {
	    if (prune_match(e, c)) return TRUE;
	}
} else {
	for (e = table1[h]; e != NULL; e = e->next) {
	    if (prune_match(c, e)) return TRUE;
	}
}
return FALSE;
}
void clean_up(int w) {
Disjunct head_disjunct, *d, *d1;
d = &head_disjunct;
d->next = sentence[w].d;
while(d->next != NULL) {
	if ((d->next->left == NULL) && (d->next->right == NULL)) {
	    d1 = d->next;
	    d->next = d1->next;
	    xfree((char *)d1, sizeof(Disjunct));
	} else {
	    d = d->next;
	}
}
sentence[w].d = head_disjunct.next;
}
int count_disjuncts(Disjunct * d) {
int count = 0;
for (; d!=NULL; d=d->next) {
	count++;
}
return count;
}
int count_disjuncts_in_sentence(void) {
int w, count;
count = 0;
for (w=0; w<N_words; w++) {
	count += count_disjuncts(sentence[w].d);
}
return count;
}
void prune(void) {
int N_deleted;
Disjunct *d;
Connector *e;
int w;
s_table_size = next_power_of_two_up(count_disjuncts_in_sentence());
table1 = (Connector **) xalloc(s_table_size * sizeof (Connector *));
zero_S();
N_deleted = 1;
for (;;) {
	
	for (w = 0; w < N_words; w++) {
	    for (d = sentence[w].d; d != NULL; d = d->next) {
		for (e = d->left; e != NULL; e = e->next) {
		    if (!matches_S(e, '-')) break;
		}
		if (e != NULL) {
		
		    N_deleted ++;
		    free_connectors(d->left);
		    free_connectors(d->right);
		    d->left = d->right = NULL;
		}
	    }
	    clean_up(w);
	    for (d = sentence[w].d; d != NULL; d = d->next) {
		for (e = d->right; e != NULL; e = e->next) {
		    insert_S(e);
		}
	    }
	}
	if (verbosity > 2) {
	    printf("l->r pass removed %d\n",N_deleted);
	    print_disjunct_counts();
	}
	free_S();
	if (N_deleted == 0) break;
	
	N_deleted = 0;
	for (w = N_words-1; w >= 0; w--) {
	    for (d = sentence[w].d; d != NULL; d = d->next) {
		for (e = d->right; e != NULL; e = e->next) {
		    if (!matches_S(e,'+')) break;
		}
		if (e != NULL) {
		
		    N_deleted ++;
		    free_connectors(d->left);
		    free_connectors(d->right);
		    d->left = d->right = NULL;
		}
	    }
	    clean_up(w);
	    for (d = sentence[w].d; d != NULL; d = d->next) {
		for (e = d->left; e != NULL; e = e->next) {
		    insert_S(e);
		}
	    }
	}
	if (verbosity > 2) {
	    printf("r->l pass removed %d\n",N_deleted);
	    print_disjunct_counts();
	}
	free_S();
	if (N_deleted == 0) break;
	N_deleted = 0;
}
xfree((char *)table, s_table_size * sizeof (Connector *));
}
static int dup_table_size;
static Disjunct ** dup_table;
int string_hash(char * s, int i) {
for(;*s != '\0';s++) i = i + (i<<1) + randtable[(*s + i) & (RTSIZE-1)];
return (i & (dup_table_size-1));
}
#if FALSE
int connector_matches_alam(Connector * a, Connector * b) {
char * s, * t, *u;
if (((!a->multi) && b->multi) ||
	(a->label != b->label) ||
	(a->priority != b->priority))  return FALSE;
s = a->string;
t = b->string;
while(isupper(*s) || isupper(*t)) {
	if (*s == *t) {
	    s++;
	    t++;
	} else return FALSE;
}
if (a->priority == DOWN_priority) {
	u = s;
	s = t;
	t = u;
}
while((*s != '\0') && (*t != '\0')) {
	if ((*s == *t) || (*s == '*') || (*t == '^')) {
	    s++;
	    t++;
	} else return FALSE;
}
while ((*s != '\0') && (*s == '*')) s++;
return (*s == '\0');
}
int connector_hash(Connector * c, int i) {
char * s;
s = c->string;
i = i + (i<<1) + randtable[(c->label + i) & (RTSIZE-1)];
while(isupper(*s)) {
	i = i + (i<<1) + randtable[(*s + i) & (RTSIZE-1)];
	s++;
}
return (i & (dup_table_size-1));
}
int hash_disjunct(Disjunct * d) {
int i;
Connector *e;
i = 0;
for (e = d->left ; e != NULL; e = e->next) {
	i = connector_hash(e, i);
}
for (e = d->right ; e != NULL; e = e->next) {
	i = connector_hash(e, i);
}
return string_hash(d->string, i);
}
int disjunct_matches_alam(Disjunct * d1, Disjunct * d2) {
Connector *e1, *e2;
if (d1->cost > d2->cost) return FALSE;
e1 = d1->left;
e2 = d2->left;
while((e1!=NULL) && (e2!=NULL)) {
	if (!connector_matches_alam(e1,e2)) break;
	e1 = e1->next;
	e2 = e2->next;
}
if ((e1!=NULL) || (e2!=NULL)) return FALSE;
e1 = d1->right;
e2 = d2->right;
while((e1!=NULL) && (e2!=NULL)) {
	if (!connector_matches_alam(e1,e2)) break;
	e1 = e1->next;
	e2 = e2->next;
}
if ((e1!=NULL) || (e2!=NULL)) return FALSE;
return (strcmp(d1->string, d2->string) == 0);
}
Disjunct * eliminate_duplicate_disjuncts(Disjunct * d) {
int i, h, count;
Disjunct *dn, *dx, *dxn, *front;
count = 0;
dup_table_size = next_power_of_two_up(2 * count_disjuncts(d));
dup_table = (Disjunct **) xalloc(dup_table_size * sizeof(Disjunct *));
for (i=0; i<dup_table_size; i++) dup_table[i] = NULL;
for (;d!=NULL; d = dn) {
	dn = d->next;
	h = hash_disjunct(d);
	front = NULL;
	for (dx = dup_table[h]; dx!=NULL; dx=dxn) {
	    dxn = dx->next;
	    if (disjunct_matches_alam(dx,d)) {
		
		d->next = NULL;
		free_disjuncts(d);
		count++;
		front = catenate_disjuncts(front, dx);
		break;
	    } else if (disjunct_matches_alam(d,dx)) {
		
		dx->next = NULL;
		free_disjuncts(dx);
		count++;
	    } else {
		
		dx->next = front;
		front = dx;
	    }
	}
	if (dx == NULL) {
	
	    d->next = front;
	    front = d;
	}
	dup_table[h] = front;
}
for (i=0; i<dup_table_size; i++) {
	for (dx = dup_table[i]; dx != NULL; dx = dxn) {
	    dxn = dx->next;
	    dx->next = d;
	    d = dx;
	}
}
xfree((char *) dup_table, dup_table_size * sizeof(Disjunct *));
if ((verbosity > 2)&&(count != 0)) printf("killed %d duplicates\n",count);
return d;
}
#endif
int old_hash_disjunct(Disjunct * d) {
int i;
Connector *e;
i = 0;
for (e = d->left ; e != NULL; e = e->next) {
	i = string_hash(e->string, i);
}
for (e = d->right ; e != NULL; e = e->next) {
	i = string_hash(e->string, i);
}
return string_hash(d->string, i);
}
int connectors_equal_prune(Connector *c1, Connector *c2) {
return (c1->label == c2->label) &&
	   (c1->multi == c2->multi) &&
	   (c1->priority == c2->priority) &&
(strcmp(c1->string, c2->string) == 0);
}
int disjuncts_equal(Disjunct * d1, Disjunct * d2) {
Connector *e1, *e2;
e1 = d1->left;
e2 = d2->left;
while((e1!=NULL) && (e2!=NULL)) {
	if (!connectors_equal_prune(e1,e2)) break;
	e1 = e1->next;
	e2 = e2->next;
}
if ((e1!=NULL) || (e2!=NULL)) return FALSE;
e1 = d1->right;
e2 = d2->right;
while((e1!=NULL) && (e2!=NULL)) {
	if (!connectors_equal_prune(e1,e2)) break;
	e1 = e1->next;
	e2 = e2->next;
}
if ((e1!=NULL) || (e2!=NULL)) return FALSE;
return (strcmp(d1->string, d2->string) == 0);
}
Disjunct * eliminate_duplicate_disjuncts(Disjunct * d) {
int i, h, count;
Disjunct *dn, *dx;
count = 0;
dup_table_size = next_power_of_two_up(2 * count_disjuncts(d));
dup_table = (Disjunct **) xalloc(dup_table_size * sizeof(Disjunct *));
for (i=0; i<dup_table_size; i++) dup_table[i] = NULL;
while (d!=NULL) {
	dn = d->next;
	h = old_hash_disjunct(d);
	for (dx = dup_table[h]; dx!=NULL; dx=dx->next) {
	    if (disjuncts_equal(dx, d)) break;
	}
	if (dx==NULL) {
	    d->next = dup_table[h];
	    dup_table[h] = d;
	} else {
	    d->next = NULL;
	    if (d->cost < dx->cost) dx->cost = d->cost;
	    free_disjuncts(d);
	    count++;
	}
	d = dn;
}
for (i=0; i<dup_table_size; i++) {
	for (dn = dup_table[i]; dn != NULL; dn = dx) {
	    dx = dn->next;
	    dn->next = d;
	    d = dn;
	}
}
xfree((char *) dup_table, dup_table_size * sizeof(Disjunct *));
if ((verbosity > 2)&&(count != 0)) printf("killed %d duplicates\n",count);
return d;
}
int size_of_sentence_expressions(void) {
X_node * x;
int w, size;
size = 0;
for (w=0; w<N_words; w++) {
	for (x=sentence[w].x; x!=NULL; x = x->next) {
	    size += size_of_expression(x->exp);
	}
}
return size;
}
int and_purge_E_list(E_list * l);
E_list * or_purge_E_list(E_list * l);
Exp* purge_Exp(Exp *e) {
if (e->type == CONNECTOR_type) {
	if (e->u.string == NULL) {
	    xfree((char *)e, sizeof(Exp));
	    return NULL;
	} else {
	    return e;
	}
}
if (e->type == AND_type) {
	if (and_purge_E_list(e->u.l) == 0) {
	    xfree((char *)e, sizeof(Exp));
	    return NULL;
	}
} else {
	e->u.l = or_purge_E_list(e->u.l);
	if (e->u.l == NULL) {
	    xfree((char *)e, sizeof(Exp));
	    return NULL;
	}
}
return e;
}
int and_purge_E_list(E_list * l) {
if (l == NULL) return 1;
if ((l->e = purge_Exp(l->e)) == NULL) {
	free_E_list(l->next);
	xfree((char *)l, sizeof(E_list));
	return 0;
}
if (and_purge_E_list(l->next) == 0) {
	free_Exp(l->e);
	xfree((char *)l, sizeof(E_list));
	return 0;
}
return 1;
}
E_list * or_purge_E_list(E_list * l) {
E_list * el;
if (l == NULL) return NULL;
if ((l->e = purge_Exp(l->e)) == NULL) {
	el = or_purge_E_list(l->next);
	xfree((char *)l, sizeof(E_list));
	return el;
}
l->next = or_purge_E_list(l->next);
return l;
}
int mark_dead_connectors(Exp * e, int dir) {
Connector dummy;
int count;
E_list *l;
dummy.label = NORMAL_LABEL;
dummy.priority = THIN_priority;
count = 0;
if (e->type == CONNECTOR_type) {
	if (e->dir == dir) {
	    dummy.string = e->u.string;
	    if (!matches_S(&dummy,dir)) {
		e->u.string = NULL;
		count++;
	    }
	}
} else {
	for (l=e->u.l; l!=NULL; l=l->next) {
	    count += mark_dead_connectors(l->e, dir);
	}
}
return count;
}
void insert_connectors(Exp * e, int dir) {
Connector dummy;
E_list *l;
dummy.label = NORMAL_LABEL;
dummy.priority = THIN_priority;
if (e->type == CONNECTOR_type) {
	if (e->dir == dir) {
	    dummy.string = e->u.string;
	    insert_S(&dummy);
	}
} else {
	for (l=e->u.l; l!=NULL; l=l->next) {
	    insert_connectors(l->e, dir);
	}
}
}
void clean_up_expressions(int w) {
X_node head_node, *d, *d1;
d = &head_node;
d->next = sentence[w].x;
while(d->next != NULL) {
	if (d->next->exp == NULL) {
	    d1 = d->next;
	    d->next = d1->next;
	    xfree((char *)d1, sizeof(X_node));
	} else {
	    d = d->next;
	}
}
sentence[w].x = head_node.next;
}
void expression_prune(void){
int N_deleted;
X_node * x;
int w;
s_table_size = next_power_of_two_up(size_of_sentence_expressions());
table1 = (Connector **) xalloc(s_table_size * sizeof (Connector *));
zero_S();
N_deleted = 1;
for (;;) {
	
	for (w = 0; w < N_words; w++) {
	    for (x = sentence[w].x; x != NULL; x = x->next) {
		N_deleted += mark_dead_connectors(x->exp, '-');
	    }
	    for (x = sentence[w].x; x != NULL; x = x->next) {
		x->exp = purge_Exp(x->exp);
	    }
	    clean_up_expressions(w);
	    for (x = sentence[w].x; x != NULL; x = x->next) {
		insert_connectors(x->exp,'+');
	    }
	}
	if (verbosity > 2) {
	    printf("l->r pass removed %d\n",N_deleted);
	    print_expression_sizes();
	}
	free_S();
	if (N_deleted == 0) break;
	
	N_deleted = 0;
	for (w = N_words-1; w >= 0; w--) {
	    for (x = sentence[w].x; x != NULL; x = x->next) {
		N_deleted += mark_dead_connectors(x->exp, '+');
	    }
	    for (x = sentence[w].x; x != NULL; x = x->next) {
		x->exp = purge_Exp(x->exp);
	    }
	    clean_up_expressions(w);
	    for (x = sentence[w].x; x != NULL; x = x->next) {
		insert_connectors(x->exp, '-');
	    }
	}
	if (verbosity > 2) {
	    printf("r->l pass removed %d\n",N_deleted);
	    print_expression_sizes();
	}
	free_S();
	if (N_deleted == 0) break;
	N_deleted = 0;
}
xfree((char *)table, s_table_size * sizeof (Connector *));
}
typedef struct c_list_struct C_list;
struct c_list_struct {
Connector * c;
int shallow;
C_list * next;
};
static int power_cost;
static int power_prune_mode;
int left_connector_count(Disjunct * d) {
Connector *c;
int i=0;
for (;d!=NULL; d=d->next) {
	for (c = d->left; c!=NULL; c = c->next) i++;
}
return i;
}
int right_connector_count(Disjunct * d) {
Connector *c;
int i=0;
for (;d!=NULL; d=d->next) {
for (c = d->right; c!=NULL; c = c->next) i++;
}
return i;
}
#define BAD_WORD (MAX_SENTENCE+1)
static int l_table_size[MAX_SENTENCE];
static int r_table_size[MAX_SENTENCE];
static C_list ** l_table1[MAX_SENTENCE];
static C_list ** r_table1[MAX_SENTENCE];
void free_C_list(C_list * t) {
C_list *xt;
for (; t!=NULL; t=xt) {
	xt = t->next;
	xfree((char *)t, sizeof(C_list));
}
}
void free_power_tables(void) {
int w;
int i;
for (w=0; w<N_words; w++) {
	for (i=0; i<l_table_size[w]; i++) {
	    free_C_list(l_table1[w][i]);
	}
	xfree((char *)l_table1[w], l_table_size[w] * sizeof (C_list *));
	for (i=0; i<r_table_size[w]; i++) {
	    free_C_list(r_table1[w][i]);
	}
	xfree((char *)r_table1[w], r_table_size[w] * sizeof (C_list *));
}
}
int power_hash(Connector * c) {
char *s;
int i;
i = randtable[c->label & (RTSIZE-1)];
s = c->string;
while(isupper(*s)) {
	i = i + (i<<1) + randtable[((*s) + i) & (RTSIZE-1)];
	s++;
}
return i;
}
void put_into_power_table(int size, C_list ** t, Connector * c, int shal ) {
int h;
C_list * m;
h = power_hash(c) & (size-1);
m = (C_list *) xalloc (sizeof(C_list));
m->next = t[h];
t[h] = m;
m->c = c;
m->shallow = shal;
}
int set_dist_fields(Connector * c, int w, int delta) {
int i;
if (c==NULL) return w;
i = set_dist_fields(c->next, w, delta) + delta;
c->word = i;
return i;
}
void init_power(void) {
int w, len, size, i;
C_list ** t;
Disjunct * d, * xd, * head;
Connector * c;
for (w=0; w<N_words; w++) {
head = NULL;
for (d=sentence[w].d; d!=NULL; d=xd) {
xd = d->next;
if ((set_dist_fields(d->left, w, -1) < 0) ||
(set_dist_fields(d->right, w, 1) >= N_words)) {
d->next = NULL;
free_disjuncts(d);
} else {
d->next = head;
head = d;
}
}
sentence[w].d = head;
}
for (w=0; w<N_words; w++) {
	len = left_connector_count(sentence[w].d);
	size = next_power_of_two_up(len);
	l_table_size[w] = size;
	t = l_table1[w] = (C_list **) xalloc(size * sizeof(C_list *));
	for (i=0; i<size; i++) t[i] = NULL;
	for (d=sentence[w].d; d!=NULL; d=d->next) {
	    c = d->left;
	    if (c != NULL) {
		put_into_power_table(size, t, c, TRUE);
		for (c=c->next; c!=NULL; c=c->next){
		    put_into_power_table(size, t, c, FALSE);
		}
	    }
	}
	len = right_connector_count(sentence[w].d);
	size = next_power_of_two_up(len);
	r_table_size[w] = size;
	t = r_table1[w] = (C_list **) xalloc(size * sizeof(C_list *));
	for (i=0; i<size; i++) t[i] = NULL;
	for (d=sentence[w].d; d!=NULL; d=d->next) {
	    c = d->right;
	    if (c != NULL) {
		put_into_power_table(size, t, c, TRUE);
		for (c=c->next; c!=NULL; c=c->next){
		    put_into_power_table(size, t, c, FALSE);
		}
	    }
	}
}
}
void clean_table(int size, C_list ** t) {
int i;
C_list * m, * xm, * head;
for (i=0; i<size; i++) {
	head = NULL;
	for (m=t[i]; m!=NULL; m=xm) {
	    xm = m->next;
	    if (m->c->word != BAD_WORD) {
		m->next = head;
		head = m;
	    } else {
		xfree((char *) m, sizeof(C_list));
	    }
	}
	t[i] = head;
}
}
int possible_connection(Connector *lc, Connector *rc,
int lshallow, int rshallow,
int lword, int rword) {
if ((!lshallow) && (!rshallow)) return FALSE;
if ((lc->word > rword) || (rc->word < lword)) return FALSE;
if (power_prune_mode == RUTHLESS) {
	if (lword == rword-1) {
	    if (!((lc->next == NULL) && (rc->next == NULL))) return FALSE;
	} else {
	    if ((!null_links) &&
		(lc->next == NULL) && (rc->next == NULL) && (!lc->multi) && (!rc->multi)) {
		return FALSE;
	    }
	}
	return match(lc, rc);
} else {
	if (lword == rword-1) {
	    if (!((lc->next == NULL) && (rc->next == NULL))) return FALSE;
	} else {
	    if ((!null_links) &&
		(lc->next == NULL) && (rc->next == NULL) && (!lc->multi) && (!rc->multi) &&
		!deletable[lword][rword]) {
		return FALSE;
	    }
	}
	return prune_match(lc, rc);
}
}
int right_table_search(int w, Connector *c, int shallow, int word_c) {
int size, h;
C_list *cl;
size = r_table_size[w];
h = power_hash(c) & (size-1);
for (cl = r_table1[w][h]; cl!=NULL; cl = cl->next) {
if (possible_connection(cl->c, c, cl->shallow, shallow, w, word_c)) {
return TRUE;
}
}
return FALSE;
}
int left_table_search(int w, Connector *c, int shallow, int word_c) {
int size, h;
C_list *cl;
size = l_table_size[w];
h = power_hash(c) & (size-1);
for (cl = l_table1[w][h]; cl!=NULL; cl = cl->next) {
if (possible_connection(c, cl->c, shallow, cl->shallow, word_c, w)) {
return TRUE;
}
}
return FALSE;
}
static int N_changed;
int ok_cwords(Connector *c){
for (; c != NULL; c=c->next) {
	if (c->word == BAD_WORD) return FALSE;
	if (c->word >= N_words) return FALSE;
}
return TRUE;
}
int left_connector_list_update(Connector *c, int word_c, int w, int shallow) {
int n;
int foundmatch;
if (c==NULL) return w;
n = left_connector_list_update(c->next, word_c, w, FALSE) - 1;
if (((int) c->word) < n) n = c->word;
foundmatch = FALSE;
for (; (n >= 0) && ((w-n) <= maxlinklength); n--) {
	power_cost++;
	if (right_table_search(n, c, shallow, word_c)) {
	    foundmatch = TRUE;
	    break;
	}
}
if (n < ((int) c->word)) {
	c->word = n;
	N_changed++;
}
return (foundmatch ? n : -1);
}
int right_connector_list_update(Connector *c, int word_c, int w, int shallow) {
int n;
int foundmatch;
if (c==NULL) return w;
n = right_connector_list_update(c->next, word_c, w, FALSE) + 1;
if (c->word > n) n = c->word;
foundmatch = FALSE;
for (; (n < N_words) && ((n-w) <= maxlinklength); n++) {
	power_cost++;
	if (left_table_search(n, c, shallow, word_c)) {
	    foundmatch = TRUE;
	    break;
	}
}
if (n > c->word) {
	c->word = n;
	N_changed++;
}
return (foundmatch ? n : N_words);
}
void power_prune(int mode) {
Disjunct *d, *free_later, *dx, *nd;
Connector *c;
int w, N_deleted;
power_prune_mode = mode;
init_power();
power_cost = 0;
free_later = NULL;
N_changed = 1;
N_deleted = 0;
for (;;) {
	
	
	for (w = 0; w < N_words; w++) {
	    for (d = sentence[w].d; d != NULL; d = d->next) {
		if (d->left == NULL) continue;
		if (left_connector_list_update(d->left, w, w, TRUE) < 0) {
		    for (c=d->left  ;c!=NULL; c = c->next) c->word = BAD_WORD;
		    for (c=d->right ;c!=NULL; c = c->next) c->word = BAD_WORD;
		    N_deleted++;
		}
	    }
	
	    clean_table(r_table_size[w], r_table1[w]);
	    nd = NULL;
	    for (d = sentence[w].d; d != NULL; d = dx) {
		dx = d->next;
		if ((d->left != NULL) && (d->left->word == BAD_WORD)) {
		    d->next = free_later;
		    free_later = d;
		} else {
		    d->next = nd;
		    nd = d;
		}
	    }
	    sentence[w].d = nd;
	}
	if (verbosity > 2) {
	   printf("l->r pass changed %d and deleted %d\n",N_changed,N_deleted);
	}
	if (N_changed == 0) break;
	
	N_changed = N_deleted = 0;
	
	
	for (w = N_words-1; w >= 0; w--) {
	    for (d = sentence[w].d; d != NULL; d = d->next) {
		if (d->right == NULL) continue;
		if (right_connector_list_update(d->right,w,w,TRUE) >= N_words){
		    for (c=d->right;c!=NULL; c = c->next) c->word = BAD_WORD;
		    for (c=d->left ;c!=NULL; c = c->next) c->word = BAD_WORD;
		    N_deleted++;
		}
	    }
	    clean_table(l_table_size[w], l_table1[w]);
	    nd = NULL;
	    for (d = sentence[w].d; d != NULL; d = dx) {
		dx = d->next;
		if ((d->right != NULL) && (d->right->word == BAD_WORD)) {
		    d->next = free_later;
		    free_later = d;
		} else {
		    d->next = nd;
		    nd = d;
		}
	    }
	    sentence[w].d = nd;
	}
	
	if (verbosity > 2) {
	   printf("r->l pass changed %d and deleted %d\n",N_changed,N_deleted);
	}
	if (N_changed == 0) break;
	N_changed = N_deleted = 0;
}
free_disjuncts(free_later);
free_power_tables();
if (verbosity > 2) printf("%d power prune cost:\n", power_cost);
}

/* 当前文件是D:\Read\strncasecmp.c*/

#ifdef TEST
int strncasecmp(const char *s1, const char *s2, size_t n);
int main (int argc, char *argv[]) {
	if (argc != 4) {
		printf ("test [string1] [string2] [size]\n");
		exit (1);
	}
	printf ("'%s' cmp '%s' = %d\n", argv[1], argv[2], strncasecmp(argv[1], argv[2], atoi(argv[3])));
	return 0;
}
#endif
int strncasecmp(const char *s1, const char *s2, size_t n)
{
	const char *i, *j;
	char ui, uj;
	for (i = s1, j = s2 ; *i!=0 && *j!=0; i++, j++ ) {
		if (n-- == 0) return 0;
		ui = toupper(*i);
		uj = toupper(*j);
		if (ui < uj) {
			return -1;
		} else if (ui > uj) {
			return 1;
		}
	}
	if (*i) return -1;
	if (*j) return  1;
	return 0;
}
/* 当前文件是D:\Read\utilities.c*/

void free_connectors(Connector *e) {
Connector * n;
for(;e != NULL; e = n) {
	n = e->next;
	xfree((char *)e, sizeof(Connector));
}
}
void free_disjuncts(Disjunct *c) {
Disjunct *c1;
for (;c != NULL; c = c1) {
	c1 = c->next;
	free_connectors(c->left);
	free_connectors(c->right);
	xfree((char *)c, sizeof(Disjunct));
}
}
void free_X_nodes(X_node * x) {
X_node * y;
for (; x!= NULL; x = y) {
	y = x->next;
	free_Exp(x->exp);
	xfree((char *)x, sizeof(X_node));
}
}
void free_E_list(E_list *);
void free_Exp(Exp * e) {
if (e->type != CONNECTOR_type) {
	free_E_list(e->u.l);
}
xfree((char *)e, sizeof(Exp));
}
void free_E_list(E_list * l) {
if (l == NULL) return;
free_E_list(l->next);
free_Exp(l->e);
xfree((char *)l, sizeof(E_list));
}
int size_of_expression(Exp * e) {
int size;
E_list * l;
if (e->type == CONNECTOR_type) return 1;
size = 0;
for (l=e->u.l; l!=NULL; l=l->next) {
	size += size_of_expression(l->e);
}
return size;
}
/*unsigned int randtable[RTSIZE];*/
#if ! defined FOR_RELEASE
void init_randtable(void) {
int i;
srandom(10);
for (i=0; i<RTSIZE; i++) {
	randtable[i] = random();
}
}
#else
void init_randtable(void) {
int i;
srand(10);
for (i=0; i<RTSIZE; i++) {
	randtable[i] = rand();
}
}
#endif
E_list * copy_E_list(E_list * l);
Exp * copy_Exp(Exp * e) {
Exp * n;
if (e == NULL) return NULL;
n = (Exp *) xalloc(sizeof(Exp));
*n = *e;
if (e->type != CONNECTOR_type) {
	n->u.l = copy_E_list(e->u.l);
}
return n;
}
E_list * copy_E_list(E_list * l) {
E_list * nl;
if (l == NULL) return NULL;
nl = (E_list *) xalloc(sizeof(E_list));
*nl = *l;
nl->next = copy_E_list(l->next);
nl->e = copy_Exp(l->e);
return nl;
}
Connector * copy_connectors(Connector * c) {
Connector *c1;
if (c == NULL) return NULL;
c1 = (Connector *) xalloc(sizeof(Connector));
*c1 = *c;
c1->next = copy_connectors(c->next);
return c1;
}
Disjunct * copy_disjunct(Disjunct * d) {
Disjunct * d1;
if (d == NULL) return NULL;
d1 = (Disjunct *) xalloc(sizeof(Disjunct));
*d1 = *d;
d1->next = NULL;
d1->left = copy_connectors(d->left);
d1->right = copy_connectors(d->right);
return d1;
}
typedef struct string_node_struct String_node;
struct string_node_struct {
char * string;
int size;
String_node * next;
};
static String_node * string_list = NULL;
void free_this_string_later(char * s, int size) {
String_node * sn;
sn = (String_node *) xalloc(sizeof(String_node));
sn->next = string_list;
string_list = sn;
sn->string = s;
sn->size = size;
}
void free_strings(void) {
String_node * sn;
for (; string_list != NULL; string_list = sn) {
	sn = string_list->next;
	xfree((char *) string_list->string, string_list->size);
	xfree((char *) string_list, sizeof(String_node));
}
}
Disjunct * catenate_disjuncts(Disjunct *d1, Disjunct *d2) {
Disjunct * dis = d1;
if (d1 == NULL) return d2;
if (d2 == NULL) return d1;
while (dis->next != NULL) dis = dis->next;
dis->next = d2;
return d1;
}
X_node * catenate_X_nodes(X_node *d1, X_node *d2) {
X_node * dis = d1;
if (d1 == NULL) return d2;
if (d2 == NULL) return d1;
while (dis->next != NULL) dis = dis->next;
dis->next = d2;
return d1;
}
int next_power_of_two_up(int i) {
int j=1;
while(j<i) j = j<<1;
return j;
}
int upper_case_match(char *s, char *t) {
while(isupper(*s) || isupper(*t)) {
	if (*s != *t) return FALSE;
	s++;
	t++;
}
return (!isupper(*s) && !isupper(*t));
}
void left_print_string(FILE * fp, char * s, char * t) {
int i, j, k;
j = strlen(t);
k = strlen(s);
for (i=0; i<j; i++) {
	if (i<k) {
	    fprintf(fp, "%c", s[i]);
	} else {
	    fprintf(fp, "%c", t[i]);
	}
}
}
/* 当前文件是D:\Read\word-file.c*/

static Word_file * word_file_header = NULL;
char * get_a_word(FILE * fp) {
char word[MAX_WORD];
char * s;
int c, j;
do {
	c = getc(fp);
} while ((c != EOF) && isspace(c));
if (c == EOF) return NULL;
for (j=0; (j<MAX_WORD) && (!isspace(c)) && (c != EOF); j++) {
	word[j] = c;
	c = getc(fp);
}
if (j == MAX_WORD) {
	error("The dictionary contains a word that is too long.");
}
word[j] = '\0';
s = (char *) xalloc(strlen(word)+1);
strcpy(s, word);
return s;
}
Dict_node * read_word_file(Dict_node * dn, char * filename) {
Dict_node * dn_new;
Word_file * wf;
FILE * fp;
char * s;
char file_name_copy[MAX_WORD];
strcpy(file_name_copy, filename+1);
if ((fp = fopen(file_name_copy, "r")) == NULL) {
	printf("\nCannot open file %s\n", file_name_copy);
	exit(1);
}
printf("*"); fflush(stdout);
wf = (Word_file *) xalloc(sizeof (Word_file));
strcpy(wf->file, file_name_copy);
wf->changed = FALSE;
wf->next = word_file_header;
word_file_header = wf;
while ((s = get_a_word(fp)) != NULL) {
	dn_new = (Dict_node *) xalloc(sizeof(Dict_node));
	dn_new->left = dn;
	dn = dn_new;
	dn->string = s;
	dn->file = wf;
}
fclose(fp);
return dn;
}
#define LINE_LIMIT 70
int xwhere_in_line;
void routput_dictionary(Dict_node * dn, FILE *fp, Word_file *wf) {
if (dn == NULL) return;
routput_dictionary(dn->left, fp, wf);
if (dn->file == wf) {
	if (xwhere_in_line+strlen(dn->string) > LINE_LIMIT) {
	    xwhere_in_line = 0;
	    fprintf(fp,"\n");
	}
	xwhere_in_line += strlen(dn->string) + 1;
	fprintf(fp,"%s ", dn->string);
}
routput_dictionary(dn->right, fp, wf);
}
void output_dictionary(Dict_node * dn, FILE *fp, Word_file *wf) {
xwhere_in_line = 0;
routput_dictionary(dn, fp, wf);
fprintf(fp,"\n");
}
void save_files(void) {
Word_file *wf;
FILE *fp;
for (wf = word_file_header; wf != NULL; wf = wf->next) {
	if (wf->changed) {
	    if ((fp = fopen(wf->file, "w")) == NULL) {
	     printf("\nCannot open %s. Gee, this shouldn't happen.\n", wf->file);
printf("file not saved\n");
	     return;
	    }
	    printf("   saving file \"%s\"\n", wf->file);
	    output_dictionary(dict_root, fp, wf);
	    fclose(fp);
	    wf->changed = FALSE;
	}
}
}
int files_need_saving(void) {
Word_file *wf;
for (wf = word_file_header; wf != NULL; wf = wf->next) {
	if (wf->changed) return TRUE;
}
return FALSE;
}

