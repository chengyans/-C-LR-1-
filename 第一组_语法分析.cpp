#include<iostream>
#include<algorithm>
#include<vector>
#include<map>
#include<string>
#include<iomanip>
#include<string>
#include <fstream>
#include <sstream>
#include<stdlib.h>
#include<stack>
#include<iomanip>
#include<queue>
#include<set>
#include<unordered_map>
#define null -1
#define $    -2
#define bg 1001
using namespace std;
/*文法描述类：left为->左侧，right为文法右侧，
以int型表示终结符和非终结符,dot的位置通过dotPosition描述*/
set<int>					terminal;
set<int>					unTerminal;
vector < pair<int, vector<int>>>gram;
map<int, string>m;
vector<pair<string, int>> allword;
vector<pair<string, int>> wrong_word;
vector<int>				 course;//最左规约的过程.
class Item {
public:
	int			        left;
	vector<int>			right;
	int 				dotPosition;
	int 				idx;						//表示该项目的由哪一个初始文法规约而来
	int  				expidx;						//表示该项目的文法在拓展文法中的位置
	bool 				isExpend;					//判断是否是拓展文法即是否有点
	int   				size;						//获取当前文法的右侧size
	Item(int l, vector<int> r, int pos, bool sign) {
		this->left = l;
		this->right = r;
		this->size = r.size() + 1;
		this->dotPosition = pos;
		this->isExpend = sign;
	}
	vector<int> expDot();									//根据dotPosition获得vector
	Item* getExpend(int, int);										//获得vector
	bool equals(const Item&);								//重载等号运算符
};
bool Item::equals(const Item& b) {
	if (this->isExpend != b.isExpend) {
		return false;
	}
	if (this->left != b.left) {
		return false;
	}
	if (this->size != b.size) {
		return false;
	}
	if (this->dotPosition != b.dotPosition) {
		return false;
	}
	int len = this->right.size();
	for (int i = 0; i<len; i++) {
		if (this->right[i] != b.right[i]) {
			return false;
		}
	}
	return true;
}
class CFG
{
public:
	set<int>							terSymbol;			//终结符
	set<int>							unTerSymbol;		//非终结符
	vector < pair<int, vector<int>>>		gram;			//初始表示文法		
	vector<Item*>						initalItems;		//初始文化
	vector<Item*>						expendItems;		//拓展文法
	unordered_map<int, set<int>>			firstSet;		//计算单个字符的First集
	CFG() {}
	CFG(set<int> terminal, set<int> unterminal, vector <pair<int, vector<int>>>g) {
		this->terSymbol = terminal;
		this->unTerSymbol = unterminal;
		this->gram = g;

	}
	void getInitItems();										//获取初始文法
	void getLRItems();										//获得拓展文法
	set<int> getFirstSet(int num,set<int>);								//计算每个字符的First集
	set<int> calFirstSet(vector<int>);							//计算字符串的First集
};
class Closure
{
public:
	vector<pair<Item*, int>>family;						//当前集族的闭包
	int 	initalSize;
	void buildFamilySign(Item*, int, CFG&, bool);	 	//根据传递来的数据构造闭包
	void buildFamily(CFG&);
	bool isInClosure(Item*, int);					//判断当前LR(1)项目是否在该闭包内
	Closure(vector<pair<Item*, int>> F) {
		this->family = F;
		this->initalSize = F.size();
	}
};
void printClosure(Closure& t);
class table {
public:
	CFG											cfggram;				//生成文法
	vector<Closure>								cfgClosures;			//生成闭包
	map<int, vector<pair<int, int>>>			actionetab;				//ACTION表，表示跳转，正数表示跳转到一定位置，负数表示使用文法进行规约。1W表示全部OK。
	map<int, vector<pair<int, int>>>			gototab;				//goto表，正数表示跳转到一定位置，0表示啥也不干。
	void buildTable();													//生成Action表和goto表
	table(CFG c) {
		this->cfggram = c;
	}
};
//构造闭包
void table::buildTable() {//使用宽度优先遍历的方法构造table
	vector<pair<Item*, int>> initClosuer = { { this->cfggram.expendItems[0],-2 } };//表示一开始的文法
	Closure ifir(initClosuer);
	ifir.buildFamily(this->cfggram);
	//printClosure(ifir);
	this->cfgClosures.push_back(ifir);
	int idx = 0;
	queue<Closure> dfsClosure;
	dfsClosure.push(ifir);
	while (!dfsClosure.empty()) {
		Closure tmp = dfsClosure.front();
		dfsClosure.pop();
		map<int, vector<pair<Item*, int>>> m;//表示本次生成的NEXT文法,int表示转换条件，num为接受
		for (auto& p : tmp.family) {
			if (p.first->dotPosition == p.first->right.size() - 1) {//表示不必规约接受即可
				if (p.second == -2 && p.first->left == 1 && p.first->right[0] == bg) {//表示为acc的情况
					actionetab[idx].push_back({ p.second,10000 });//表示规约，按照第i个文法
				}
				else {
					actionetab[idx].push_back({ p.second,-p.first->idx });
				}
			}
			else {
				int idex = p.first->dotPosition + 1;//idex表示位置
				int t = p.first->right[idex];//表示.之后的字符
				m[t].push_back({ this->cfggram.expendItems[p.first->expidx + 1],p.second });//获取后面的的CLOSURE
			}
		}
		for (auto&p : m) {//p.first=int,表示下一个字符,p.second=vector<pair<Item*,int>>表示转换后的情况
			bool judge = false;
			Closure newClo(p.second);//新项目集初始化
			newClo.buildFamily(this->cfggram);//构造新的项目集
			for (int i = 0; i < cfgClosures.size(); i++) {
				if (cfgClosures[i].family.size() == newClo.family.size()) {//此时表示已经有项目集产生了，只需要加入其中便可.
					int j = 0;
					for (j = 0; j<newClo.family.size(); j++) {
						if (!cfgClosures[i].isInClosure(newClo.family[j].first, newClo.family[j].second)) {
							break;
						}
					}
					if (j == newClo.family.size()) {
						if (this->cfggram.terSymbol.count(p.first)) {//表示为终结符
							actionetab[idx].push_back({ p.first,i });//表示进行移进
						}
						else {
							gototab[idx].push_back({ p.first,i });
						}
						judge = true;
						break;
					}
				}
			}
			if (!judge) {//没有找到匹配的项目集，需要构造新的项目
				dfsClosure.push(newClo);
				cfgClosures.push_back(newClo);
				if (this->cfggram.terSymbol.count(p.first)) {
					actionetab[idx].push_back({ p.first,cfgClosures.size() - 1 });//表示此时为最后一个
				}
				else {
					gototab[idx].push_back({ p.first,cfgClosures.size() - 1 });
				}
			}
		}
		idx++;
	}
}
bool Closure::isInClosure(Item* waitCmp, int waitNum) {
	for (auto& p : family) {
		if (p.first->equals(*waitCmp) && p.second == waitNum) {
			return true;
		}
	}
	return false;
}
void Closure::buildFamily(CFG& gram) {
	for (int i = 0; i<initalSize; i++) {
		if (family[i].first->dotPosition != family[i].first->right.size() - 1) {
			buildFamilySign(family[i].first, family[i].second, gram, false);
		}
	}
}
void Closure::buildFamilySign(Item* init, int initNum, CFG& gram, bool judge) {
	if (judge&&isInClosure(init, initNum)) {
		return;
	}
	if (judge && (init->dotPosition == init->right.size() - 1 || gram.terSymbol.count(init->right[init->dotPosition + 1]))) {
		this->family.push_back({ init,initNum });
		return;
	}
	if (judge) {
		this->family.push_back({ init,initNum });
	}
	int nextWait = init->right[init->dotPosition + 1];		//表示dot后面的第一个非终结符
	vector<int> follow;										//为非终结符后面的符号集合
	int beginPos = init->dotPosition + 2;
	for (int i = beginPos; i<init->right.size(); i++) {
		follow.push_back(init->right[i]);
	}
	follow.push_back(initNum);
	set<int>first = gram.calFirstSet(follow);//寻找后序集合的First集
											 //寻找以dot后面开头的非终结符的文法并与first中的文法组合
	for (auto p : gram.expendItems) {
		if (p->left == nextWait&&p->dotPosition == 0) {
			for (auto num : first) {
				buildFamilySign(p, num, gram, true);
			}
		}
	}
}
vector<int> Item::expDot() {
	int len = this->right.size(), i = 0, j = 0;
	vector<int> res = vector<int>(len + 1, 0);
	while (i != len + 1) {
		if (i == this->dotPosition) {
			res[i++] = 0;
		}
		else {
			res[i++] = this->right[j++];
		}
	}
	return res;
}
Item* Item::getExpend(int idx, int expidx) {
	int len = this->right.size();
	if (dotPosition>len) {
		return nullptr;
	}
	vector<int>nRight = expDot();
	Item* res = new Item(this->left, nRight, this->dotPosition++, true);
	res->idx = idx;
	res->expidx = expidx;
	return res;
}
//CFG 获得初始文法：
void CFG::getInitItems() {
	for (auto& p : gram) {
		Item* inital = new Item(p.first, p.second, 0, false);
		this->initalItems.push_back(inital);
	}
}
//CFG 获得拓展文法:
void CFG::getLRItems() {
	int idx = 0, idx2 = 0;
	for (auto& item : this->initalItems) {
		while (item->dotPosition != item->size) {
			Item* tmp = item->getExpend(idx, idx2++);
			this->expendItems.push_back(tmp);
		}
		idx++;
	}
}
//获取当前字符的First集
set<int> CFG::getFirstSet(int num,set<int>allnum) {
	if (!terSymbol.count(num) && !unTerSymbol.count(num)) {
		return{};
	}
	set<int>res;
	if (firstSet.count(num)) {
		return firstSet[num];
	}//记忆化搜索
	if (terSymbol.count(num)) {
		res.insert(num);
		firstSet.insert({ num,res });//处理终结符的first集
		return res;
	}
	else {
		for (auto& item : initalItems) {
			if (item->left == num) {
				int idx = 1;
				for (int i = 0; i<idx; i++) {
					if (item->right.size() == 1 && item->right[0] == -1) {
						res.insert(-1);
					}//表示当前情况下只有一个空
					else {
						if (!allnum.count(item->right[i])) {
							allnum.insert(item->right[i]);
							set<int>tmp = getFirstSet(item->right[i],allnum);
							for (int n : tmp) {
								if (n == -1) {
									idx++;//表示当前情况下含有空，则First集可以后推
								}
								res.insert(n);
							}
						}
					}
				}
			}
		}
		this->firstSet.insert({ num,res });
	}
	return res;
}
set<int> CFG::calFirstSet(vector<int> nums) {
	set<int>res;
	int befIdx = -1;
	int idx = 0;
	while (idx<nums.size() && idx != befIdx) {
		befIdx = idx;
		set<int>tmp = getFirstSet(nums[idx], {nums[idx]});
		for (auto& n : tmp) {
			if (n == -1) {
				idx++;
				res.insert(-1);
			}
			else {
				res.insert(n);
			}
		}
	}
	return res;
}
void loadTerm(set<int>& terSymbol) {
	terSymbol= { 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,
		21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,
		41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,
		61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,100,200,-2 };
}
void loadUnter(set<int>&	unTerSymbol) {
	unTerSymbol = { 1001,1002,1003,1004,1005,1006,1007,1008,1009,1010,
		1011,1012,1013,1014,1015,1016,1017,1018,1019,1020,1021,1022,
		1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,
	1037,1038};
}
void loadGram(vector<pair<int, vector<int>>>& gram){
	gram.push_back({ 1,{ 1001 } });
	/*
	gram.push_back({ 1020,{ 16,61,1023,62,1014 } });
	gram.push_back({ 1020,{ 16,61,1023,62,1014,10,1014 } });
	gram.push_back({ 1021,{ 32,61,1023,62,1014 } });
	gram.push_back({ 1021,{ 14,61,1019,1019,62,1014 } });
	gram.push_back({ 1021,{ 14,61,1019,1019,1023,62,1014 } });
	gram.push_back({ 1022,{ 6,60 } });
	gram.push_back({ 1022,{ 2,60 } });
	gram.push_back({ 1022,{ 20,60 } });
	gram.push_back({ 1022,{ 20,1023,60 } });
	gram.push_back({ 1023,{ 1026 } });
	gram.push_back({ 1023,{ 1008 } });

	//
	
	//gram.push_back({ 1028,{ 1008,67,1023,68,1023 } });
	*/
	gram.push_back({ 1001,{ 1002 } });
	gram.push_back({ 1001,{ 1001,1002 } });	//添加总控程序
	gram.push_back({ 1002,{ 1004 } });
	gram.push_back({ 1004,{ 1011 } });
	gram.push_back({ 1004,{ 1034 } });
	gram.push_back({ 1004,{ 1019 } });
	gram.push_back({ 1011, { 1005,1006,61,1010,62,60 } });
	gram.push_back({ 1011,{ 1005,1006,61,62,60 } });
	gram.push_back({ 1010,{ 1005 } });
	gram.push_back({ 1010,{ 1010,59,1005 } });
	gram.push_back({ 1002,{ 1003 } });	/////////////////////////////////////////函数块fuck gc
	gram.push_back({ 1003,{ 1005,1006,61,1009,62,1014 } });
	gram.push_back({ 1003,{ 1005,1006,61,62,1014 } });
	gram.push_back({ 1005,{ 30 } });
	gram.push_back({ 1005,{ 4 } });
	gram.push_back({ 1005,{ 17 } });
	gram.push_back({ 1005,{ 13 } });
	gram.push_back({ 1006,{ 200 } });
	gram.push_back({ 1009,{ 1005,200 } });
	gram.push_back({ 1009,{ 1009,59,1005,200 } });
	gram.push_back({ 1014,{ 65,66 } });
	gram.push_back({ 1014,{ 65,1015,66 } });
	gram.push_back({ 1015,{ 1015,1016 } });
	gram.push_back({ 1015,{ 1016 } });
	gram.push_back({ 1016,{ 1037 } });//表示函数调用语句
	gram.push_back({ 1037,{ 1017,60 } });
	gram.push_back({ 1017,{ 1006,61,1007,62} });
	gram.push_back({ 1017,{ 1006,61,62 } });
	gram.push_back({ 1006,{ 200 } });
	gram.push_back({ 1007,{ 1008 } });
	gram.push_back({ 1007,{ 1007,59,1008 } });
	gram.push_back({ 1016,{ 1020 } });
	gram.push_back({ 1020,{ 16,61,1023,62,1014 } });
	gram.push_back({ 1020,{ 16,61,1023,62,1014,10,1014 } });
	gram.push_back({ 1016,{ 1021 } });
	gram.push_back({ 1021,{ 32,61,1023,62,1014 } });
	gram.push_back({ 1021,{ 14,61,1019,1019,62,1014 } });
	gram.push_back({ 1021,{ 14,61,1034,1019,62,1014 } });
	gram.push_back({ 1021,{ 14,61,1019,1019,1023,62,1014 } });
	gram.push_back({ 1021,{ 14,61,1034,1019,1023,62,1014 } });
	gram.push_back({ 1016,{ 1022 } });
	gram.push_back({ 1022,{ 6,60 } });
	gram.push_back({ 1022,{ 2,60 } });
	gram.push_back({ 1022,{ 20,60 } });
	gram.push_back({ 1022,{ 20,1023,60 } });
	gram.push_back({ 1016,{ 1034 } });
	gram.push_back({ 1034,{ 1035,60 } });
	gram.push_back({ 1035,{ 1005,1036 } });
	gram.push_back({ 1035,{ 1035,59,1036 } });
	gram.push_back({ 1036,{ 1030 } });
	gram.push_back({ 1036,{ 200 } });
	gram.push_back({ 1016,{ 1019 } });
	gram.push_back({ 1019,{ 60 } });
	gram.push_back({ 1019,{ 1023,60 } });
	gram.push_back({ 1023,{1026} });
	gram.push_back({ 1023,{ 1008 } });
	gram.push_back({ 1023,{ 1023,59,1026 } });
	gram.push_back({ 1026,{ 1029 } });
	gram.push_back({ 1026,{ 1028 } });
	gram.push_back({ 1028,{ 1023,67,1023,68,1023 } });
	gram.push_back({ 1008,{ 200 } });
	gram.push_back({ 1008,{ 100 } });
	gram.push_back({ 1029,{ 1030 } });
	gram.push_back({ 1029,{ 1032 } });
	gram.push_back({ 1030,{ 200,1031,1023 } });
	gram.push_back({ 1030,{ 200,1031,1017 } });
	gram.push_back({ 1032,{ 1023,1033,1023 } });
	gram.push_back({ 1031,{ 33 } });
	gram.push_back({ 1031,{ 38 } });
	gram.push_back({ 1031,{ 39 } });
	gram.push_back({ 1031,{ 40 } });
	gram.push_back({ 1031,{ 41 } });
	gram.push_back({ 1031,{ 42 } });
	gram.push_back({ 1033,{ 34 } });
	gram.push_back({ 1033,{ 35 } });
	gram.push_back({ 1033,{ 36 } });
	gram.push_back({ 1033,{ 37 } });
	gram.push_back({ 1033,{ 43 } });
	gram.push_back({ 1033,{ 44 } });
	gram.push_back({ 1033,{ 45 } });
	gram.push_back({ 1033,{ 46 } });
	gram.push_back({ 1033,{ 47 } });
	gram.push_back({ 1033,{ 48 } });
	gram.push_back({ 1033,{ 49 } });
	gram.push_back({ 1033,{ 50 } });
	gram.push_back({ 1033,{ 51 } });
	gram.push_back({ 1033,{ 52 } });
	gram.push_back({ 1033,{ 53 } });
	gram.push_back({ 1033,{ 54 } });
	gram.push_back({ 1033,{ 55 } });
	gram.push_back({ 1033,{ 56 } });
	gram.push_back({ 1033,{ 76 } });
	gram.push_back({ 1026,{ 1037 } });
	gram.push_back({ 1037,{ 200,1038 } });
	gram.push_back({ 1037,{ 1038,200 } });
	gram.push_back({ 1038,{ 57 } });
	gram.push_back({ 1038,{ 58 } });
}
void loadSign(map<int,string>&m) {
	m.insert({ -2,"#" });
	m.insert({ 0, "." });
	m.insert({ 1, "S" });
	m.insert({ 2, "break" });
	m.insert({ 3, "case" });
	m.insert({ 4, "char" });
	m.insert({ 5, "const" });
	m.insert({ 6, "continue" });
	m.insert({ 7, "default" });
	m.insert({ 8, "do" });
	m.insert({ 9, "double" });
	m.insert({ 10, "else" });
	m.insert({ 11, "enum" });
	m.insert({ 12, "extern" });
	m.insert({ 13, "float" });
	m.insert({ 14, "for" });
	m.insert({ 15, "goto" });
	m.insert({ 16, "if" });
	m.insert({ 17, "int" });
	m.insert({ 18, "long" });
	m.insert({ 19, "register" });
	m.insert({ 20, "return" });
	m.insert({ 21, "short" });
	m.insert({ 22, "signed" });
	m.insert({ 23, "sizeof" });
	m.insert({ 24, "static" });
	m.insert({ 25, "struct" });
	m.insert({ 26, "switch" });
	m.insert({ 27, "typeof" });
	m.insert({ 28, "union" });
	m.insert({ 29, "unsigned" });
	m.insert({ 30, "void" });
	m.insert({ 31, "volatile" });
	m.insert({ 32, "while" });
	m.insert({ 33, "=" });
	m.insert({ 34, "- " });
	m.insert({ 35, "*" });
	m.insert({ 36, "/" });
	m.insert({ 37, "%" });
	m.insert({ 38, "+=" });
	m.insert({ 39, "-=" });
	m.insert({ 40, "*=" });
	m.insert({ 41, "/=" });
	m.insert({ 42, "%=" });
	m.insert({ 43, ">" });
	m.insert({ 44, "<" });
	m.insert({ 45, ">=" });
	m.insert({ 46, "<=" });
	m.insert({ 47, ">>" });
	m.insert({ 48, "<<" });
	m.insert({ 49, "==" });
	m.insert({ 50, "!=" });
	m.insert({ 51, "&" });
	m.insert({ 52, "&&" });
	m.insert({ 53, "|" });
	m.insert({ 54, "||" });
	m.insert({ 55, "&=" });
	m.insert({ 56, "|=" });
	m.insert({ 57, "++" });
	m.insert({ 58, " --" });
	m.insert({ 59, "," });
	m.insert({ 60, ";" });
	m.insert({ 61, "(" });
	m.insert({ 62, ")" });
	m.insert({ 63, "[" });
	m.insert({ 64, "]" });
	m.insert({ 65, "{" });
	m.insert({ 66, "}" });
	m.insert({ 67, "?" });
	m.insert({ 68, ":" });
	m.insert({ 69, "." });
	m.insert({ 70, "<=" });
	m.insert({ 71, ">>=" });
	m.insert({ 72, "^" });
	m.insert({ 73, "^=" });
	m.insert({ 74, "~" });
	m.insert({ 75, "::" });
	m.insert({ 76, "+" });
	m.insert({ 100, "常量" });
	m.insert({ 200, "变量名" });
	m.insert({ 1001, "程序" });
	m.insert({ 1002, "外部声明" });
	m.insert({ 1003, "函数定义" });
	m.insert({ 1004, "环境声明" });
	m.insert({ 1005, "类型名" });
	m.insert({ 1006, "函数名" });
	m.insert({ 1007, "参数序列" });
	m.insert({ 1008, "标识符" });
	m.insert({ 1009, "带类型参数序列" });
	m.insert({ 1010, "类型序列" });
	m.insert({ 1011, "函数声明" });
	m.insert({ 1012, "头文件声明" });
	m.insert({ 1013, "声明语句" });
	m.insert({ 1014, "语句块" });
	m.insert({ 1015, "语句List" });
	m.insert({ 1016, "语句" });
	m.insert({ 1017, "函数调用" });
	m.insert({ 1018, "复合语句" });
	m.insert({ 1019, "表达式语句" });
	m.insert({ 1020, "选择语句" });
	m.insert({ 1021, "循环语句" });
	m.insert({ 1022, "跳转语句" });
	m.insert({ 1023, "表达式" });
	m.insert({ 1024, "声明式" });
	m.insert({ 1025, "标识符集" });
	m.insert({ 1026, "操作语句" });
	m.insert({ 1027, "操作语句式" });
	m.insert({ 1028, "三目条件赋值" });
	m.insert({ 1029, "二目操作" });
	m.insert({ 1030, "赋值语句" });
	m.insert({ 1031, "赋值符号" });
	m.insert({ 1032, "计算语句" });
	m.insert({ 1033, "计算符号" });
	m.insert({ 1034, "变量定义语句" });
	m.insert({ 1035, "变量定义" });
	m.insert({ 1036, "待定义变量" });
	m.insert({ 1037, "单目操作" });
	m.insert({ 1038, "单目操作符" });
}
void printClosure(Closure& t) {
	for (auto& p : t.family) {
		cout << m[p.first->left]<<"		->	"	;
		for (auto&s : p.first->right) {
			cout << m[s];
		}
		cout << "	;	";
		cout << m[p.second]<<endl;
	}
}
struct buffer
{
	int max_size = 256;
	int front = 0;
	int back = 0;
	int size = 0;
	char buff[255];
}scan_buff;//表示为扫描缓冲区程序，大小为256

struct input_buffer//输入缓冲区
{
	string all;
	string next_state;
	int index;
}in_buff;
//函数声明
string readFileIntoString(char * filename);
string  pre_process(input_buffer&in_buff);
void    word_analysis();
bool isdigit(char c);
bool isletter(char c);
void retract();//往后后退一格
bool iskeywords(string tmp);//判断是否是关键字


							//全局变量

map<string, int> keywords = { { "auto",1 },{ "break",2 },{ "case",3 },{ "char",4 },{ "const",5 },{ "continue",6 },{ "default",7 },{ "do",8 },{ "double",9 },{ "else",10 },
{ "enum",11 },{ "extern",12 },{ "float",13 },{ "for",14 },{ "goto",15 },{ "if",16 },{ "int",17 },{ "long",18 },{ "register",19 },{ "return",20 },{ "short",21 },
{ "signed",22 },{ "sizeof",23 },{ "static",24 },{ "struct",25 },{ "switch",26 },{ "typeof",27 },{ "union",28 },{ "unsigned",29 },{ "void",30 },
{ "volatile",31 },{ "while",32 } };
set<char>operator_t1 = { '+','*','|','=','&','|','>','<',':' };//c,cc,c=三种都是
set<char>operator_t2 = { '/','^','%' };//c,c=
set<char>operator_t3 = { '~', ',', '[', ']', '{', '}', '(', ')', '.', '?',';' };//c
set<char>operator_t4 = { ':' };//c,cc
map<string, int> operators = { { "=",33 },{ "-",34 },{ "*",35 },{ "/",36 },{ "%",37 },{ "+=",38 },{ "-=",39 },{ "*=",40 },{ "/=",41 },{ "%=",42 },{ ">",43 },{ "<",44 },{ ">=",45 },{ "<=",46 },{ ">>",47 },{ "<<",48 },
{ "==",49 },{ "!=",50 },{ "&",51 },{ "&&",52 },{ "|",53 },{ "||",54 },{ "&=",55 },{ "|=",56 },{ "++",57 },{ "--",58 },{ ",",59 },{ ";",60 },{ "(",61 },{ ")",62 },
{ "[",63 },{ "]",64 },{ "{",65 },{ "}",66 },{ "?",67 },{ ":",68 },{ ".",69 },{ "<<=",70 },{ ">>=",71 },{ "^",72 },{ "^=",73 },{ "~",74 },{ "::",75 },{ "+",76 } };
map<string, int>symbol_table;//存储变量的符号表
set<string>symbols;
int begin_num = 200;
//从文件读入到string里
string readFileIntoString(char * filename)
{
	ifstream ifile(filename);
	//将文件读入到ostringstream对象buf中
	ostringstream buf;
	char ch;
	while (buf&&ifile.get(ch))
		buf.put(ch);
	//返回与流对象buf关联的字符串
	return buf.str();
}


//程序预处理
string pre_process(input_buffer&in_buff)//输入缓冲区预处理程序，每次调用读入一个完整的语句到扫描缓冲区中
{
	if (in_buff.next_state != "")
	{
		string tmp = in_buff.next_state;
		in_buff.next_state = "";
		return tmp;
	}
	int len = in_buff.all.size();
	int&index = in_buff.index;
	while (index < len && (in_buff.all[index] == ' ' || in_buff.all[index] == '\t'))
	{
		index++;
	}
	string res;//表示输入的条语句
	while (index < len)
	{
		if (in_buff.all[index] == '\n' || in_buff.all[index] == '\t')
		{
			index++;
			while (index < len && (in_buff.all[index] == ' ' || in_buff.all[index] == '\t'))
			{
				index++;
			}
		}
		else if (in_buff.all[index] == '{')
		{
			if (res == "")
			{
				index++;
				return "{";
			}
			else
				return  res;
		}
		else if (in_buff.all[index] == '}')
		{
			if (res == "")
			{
				index++;
				return "}";
			}
			else
				return res;
		}
		else if (in_buff.all[index] == '/')
		{
			index++;
			if (index<len&&in_buff.all[index] == '/')//出现//型注释，往后推导，直到读取到'\n'
			{
				index++;
				while (index<len&&in_buff.all[index] != '\n')
					index++;
				index++;
			}//处理结束本行
			else if (index<len&&in_buff.all[index] == '*')//出现/*的情况
			{
				index++;
				while (index<len && !(in_buff.all[index] == '*'&&in_buff.all[index + 1] == '/'))
					index++;
				index += 2;
			}
			else
				res += '/';
		}
		else
		{
			if (in_buff.all[index] != ';')
			{
				res += in_buff.all[index];
				index++;
			}
			else
			{
				res += ';';
				index++;
				return res;
			}
		}
	}
	return res;
}

bool isdigit(char c)
{
	return c >= '0'&&c <= '9';
}

bool isletter(char c)
{
	return  (c >= 'a'&&c <= 'z') || (c >= 'A'&&c <= 'Z');
}

void retract()
{
	scan_buff.back -= 1;
}

bool iskeywords(string tmp)
{
	return keywords.find(tmp) != keywords.end();
}

char getch()
{
	if (scan_buff.back < scan_buff.size)
		return scan_buff.buff[scan_buff.back];
	return ' ';
}
pair<string, int> token()//返回一个单词词组
{
	int&left = scan_buff.front;
	int&right = scan_buff.back;
	while (right < scan_buff.size&&scan_buff.buff[right] == ' ')
		right++;
	string res;
	if (isdigit(getch()))
	{
		res += getch();
		right++;
		while (isdigit(getch()))
		{
			res += getch();
			right++;
		}
		if (getch() == '.')//出现浮点数的情况
		{
			res += '.';
			right++;
			while (isdigit(getch()))
			{
				res += getch();
				right++;
			}
			if (getch() == 'E' || getch() == 'e')
			{
				res += getch();
				right++;
			}
			else
				return{ res,100 };
			int tmp = right;
			if (getch() == '-')
			{
				res += getch();
				right++;
			}
			while (isdigit(getch()))
			{
				res += getch();
				right++;
			}
			if (right == tmp || getch() == '.')
			{
				return{ "double wronng   " + res,-1 };
			}
			else
				return{ res,100 };//表示浮点型数字
		}
		else
			return{ res,100 };//表示整形数
	}
	else if (isletter(getch()) || getch() == '_')
	{
		res += getch();
		right++;
		while (isletter(getch()) || isdigit(getch()) || getch() == '_')
		{
			res += getch();
			right++;
		}
		if (iskeywords(res))
			return{ res,keywords[res] };
		else
			if (symbols.find(res) == symbols.end())
			{
				symbols.insert(res);
				symbol_table.insert({ res,begin_num });
				return{ res,begin_num };
			}
			else
			{
				return{ res,symbol_table[res] };
			}
	}
	else if (operator_t1.find(getch()) != operator_t1.end())
	{
		char c = getch();
		res += c;
		right++;
		if (getch() == '=' || getch() == c)
		{
			res += getch();
			right++;
			if ((res == "<<" || res == ">>") && getch() == '=')
			{
				res += '=';
				right++;
			}
			return{ res,operators[res] };
		}
		return{ res,operators[res] };
	}
	else if (getch() == '-')
	{
		res += '-';
		right++;
		if (getch() == '-' || getch() == '=')
		{
			res += getch();
			right++;
			return{ res,operators[res] };
		}
		else if (isdigit(getch()))
			{
				res += getch();
				right++;
				while (isdigit(getch()))
				{
					res += getch();
					right++;
				}
				if (getch() == '.')//出现浮点数的情况
				{
					res += '.';
					right++;
					while (isdigit(getch()))
					{
						res += getch();
						right++;
					}
					if (getch() == 'E' || getch() == 'e')
					{
						res += getch();
						right++;
					}
					else
						return{ res,100 };//表示浮点型数字
					int tmp = right;
					while (isdigit(getch()))
					{
						res += getch();
						right++;
					}
					if (right == tmp || getch() == '.')
					{
						return{ "double wronng   " + res,-1 };
					}
					else
						return{ res,100 };//表示浮点型数字
				}
				else
					return{ res,100 };//表示整形数
			}
		else {
			return{ res,34 };
		}
	}
	else if (operator_t2.find(getch()) != operator_t2.end())
	{
		res += getch();
		right++;
		if (getch() == '=')
		{
			res += getch();
			right++;
		}
		return{ res,operators[res] };
	}
	else if (operator_t3.find(getch()) != operator_t3.end())
	{
		res += getch();
		right++;
		return{ res,operators[res] };
	}
	else if (operator_t4.find(getch()) != operator_t4.end())
	{
		char c = getch();
		res += c;
		right++;
		if (getch() == c)
		{
			res += c;
			right++;
		}
		return{ res,operators[res] };
	}
	else if (getch() == '!')
	{
		res += getch();
		right++;
		if (getch() == '=')
		{
			res += getch();
			right++;
			return{ res,operators[res] };
		}
		return{ res,-1 };
	}
	else if (getch() == '\'')//表示char类型
	{
		res += getch();
		right++;
		char c = getch();
		right++;
		if (getch() == '\'')
		{
			right++;
			return{ res + c + '\'', 103 };
		}
		else
		{
			retract();
			return{ res,-1 };
		}
	}
	else { right++; return{ res,-1 }; };
}
void word_analysis()//对整个缓冲区进行分分析
{
	while (scan_buff.back < scan_buff.size)
	{
		pair<string, int>res = token();
		if (res.second != -1)
			allword.push_back(res);
		else
			wrong_word.push_back(res);
	}
	scan_buff.size = 0;
	scan_buff.back = 0;
	scan_buff.front = 0;
}
void getInuput(char *filename){
	in_buff.all = readFileIntoString(filename);//输入缓冲区的情况
	in_buff.index = 0;
	while(in_buff.index<in_buff.all.size()){
		string tmp=pre_process(in_buff);
		if (tmp.size() + scan_buff.size <= scan_buff.max_size){
			for (auto t : tmp)
			scan_buff.buff[scan_buff.size++] = t;
		}
		else{
		in_buff.next_state = tmp;
		word_analysis();
			}
	}
//最后的情况下扫描缓冲区为满，进行一次词法分析
	word_analysis();
}
void dividedInput(vector<string>& intial,vector<int>& travese) {
	for (auto& p : allword) {
		intial.push_back(p.first);
		travese.push_back(p.second);
	}
	intial.push_back("#");
	travese.push_back(-2);
}
int findAction(int now,int val,map<int, vector<pair<int, int>>>&actionetab) {
	for (auto& p : actionetab[now]) {
		if (p.first == val) {
			return p.second;
		}
	}
	return -10000;
}
int findGoto(int statu,int val,map<int, vector<pair<int, int>>>& gototab) {
	for (auto& p : gototab[statu]) {
		if (p.first == val) {
			return p.second;
		}
	}
	return -10000;
}
void tablePrint(vector<int>& status, vector<int>& signs, int idx,string ans,vector<int>& traverse, vector<string>& initial) {
	for (auto& s : status) {
		cout << s;
	}
	cout << "|||";
	for (auto& s : signs) {
		cout << m[s];
	}
	cout << "|||";
	cout << ans<<"|||";
	for (int i = idx; i < initial.size(); i++) {
		cout << traverse[i] << " ";
	}
	cout << endl;
}
void gramAnalysis(vector<int>& status, vector<int>& signs,vector<int>& traverse,vector<string>& initial,map<int, vector<pair<int, int>>>&actionetab,map<int,vector<pair<int, int>>>& gototab) {
	status.push_back(0);							//标识状态0
	signs.push_back(-2);							//一开始push进去
	int idx = 0;									//traverse的扫描下标
	string work;
	while (idx !=traverse.size()) {
		tablePrint(status, signs, idx, work, traverse, initial);
		work = "";
		int nextVal = traverse[idx];
		int nextStatu = findAction(status.back(),nextVal, actionetab);
		if (nextStatu != -10000) {				//可以进行移进
			if (nextStatu > 0&&nextStatu!=10000) {
				status.push_back(nextStatu);
				signs.push_back(nextVal);
				work = 's' + to_string(nextStatu);
				idx++;
			}
			else if(nextStatu<0){
				int agg = abs(nextStatu);				//表示规约的情况
				int s = gram[agg].second.size(),i=0;	//需要规约的字符的个数
				while (i < s) {
					status.pop_back();
					signs.pop_back();
					i++;
				}
				signs.push_back(gram[agg].first);
				int gtNext=findGoto(status.back(),signs.back(), gototab);
				status.push_back(gtNext);
				work = 'r' + to_string(agg)+"  goto"+to_string(gtNext);
				course.push_back(agg);
			}
			else {
				work = "acc";
				tablePrint(status, signs, idx,work, traverse, initial);
				return;
			}
		}
		else {
			cout << "WOC 出错了";
			return;
		}
	}
}
void printNode(int num,pair<int, vector<int>>& p) {//num表示空格的个数
	for (int i = 0; i < num; i++) {
		cout << " ";
	}
	cout << "|__";
	cout << "<"<<m[p.first]<<">"<<"->";
	for (auto& num : p.second) {
		cout << "<" << m[num] << "> " ;
	}
	cout << endl;
}
void printTree() {
	map<int, stack<int>>appear;
	appear[bg].push(0);
	while (!course.empty()) {
		int idx = course.back();//idx表示用第几个产生式进行规约
		printNode(appear[gram[idx].first].top(),gram[idx]);
		int n=appear[gram[idx].first].top();
		appear[gram[idx].first].pop();
		for (auto p : gram[idx].second) {
			appear[p].push(n + 1);
		}
		course.pop_back();
	}
}
int main() {
	vector<string>	initial;
	vector<int>		traverse;//输入串
	vector<int>		status;//状态
	vector<int>		signs;//符号串
	/*生成文法以及ACTION GOTO 表*/
	loadTerm(terminal);
	loadUnter(unTerminal);
	loadGram(gram);
	loadSign(m);
	CFG cfgrammer(terminal, unTerminal, gram);
	cfgrammer.getInitItems();
	cfgrammer.getLRItems();
	table t(cfgrammer);
	t.buildTable();
	char *filename = "test.txt";
	getInuput(filename);
	dividedInput(initial, traverse);
	gramAnalysis(status, signs, traverse, initial,t.actionetab,t.gototab);
	//printTree();//根据开始文法生成树。
	/*set<int> tmp = cfgrammer.getFirstSet(1017, {1017});
	for (auto& t : tmp) {
		cout << m[t] << endl;
	}*//*
	for (auto& p : cfgrammer.expendItems) {
		cout << m[p->left] << "->	";
		for (auto& num : p->right) {
			cout << m[num] << " ";
		}
		cout << endl;
	}*/
	/*
	int row = cfgrammer.unTerSymbol.size() + cfgrammer.terSymbol.size();
	cout << "ACTION表" << endl;
	for (auto p : t.actionetab) {
		cout << "状态" << p.first << "		";
		for (auto a : p.second) {
			cout << m[a.first] << "		";
			if (a.second == 10000) {
				cout << "acc";
			}
			else {
				if (a.second > 0) {
					cout << 's';
				}
				else {
					cout << 'r';
				}
				cout << abs(a.second) << "		";
			}
		}
		cout << endl;
	}
	cout << "GOTO表" << endl;
	for (auto p : t.gototab) {
		cout << "状态" << p.first << "		";
		for (auto a : p.second) {
			cout << m[a.first] << "		";
			cout << abs(a.second);
		}
		cout << endl;
	}*/
	getchar();
}