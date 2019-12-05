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
/*�ķ������ࣺleftΪ->��࣬rightΪ�ķ��Ҳ࣬
��int�ͱ�ʾ�ս���ͷ��ս��,dot��λ��ͨ��dotPosition����*/
set<int>					terminal;
set<int>					unTerminal;
vector < pair<int, vector<int>>>gram;
map<int, string>m;
vector<pair<string, int>> allword;
vector<pair<string, int>> wrong_word;
vector<int>				 course;//�����Լ�Ĺ���.
class Item {
public:
	int			        left;
	vector<int>			right;
	int 				dotPosition;
	int 				idx;						//��ʾ����Ŀ������һ����ʼ�ķ���Լ����
	int  				expidx;						//��ʾ����Ŀ���ķ�����չ�ķ��е�λ��
	bool 				isExpend;					//�ж��Ƿ�����չ�ķ����Ƿ��е�
	int   				size;						//��ȡ��ǰ�ķ����Ҳ�size
	Item(int l, vector<int> r, int pos, bool sign) {
		this->left = l;
		this->right = r;
		this->size = r.size() + 1;
		this->dotPosition = pos;
		this->isExpend = sign;
	}
	vector<int> expDot();									//����dotPosition���vector
	Item* getExpend(int, int);										//���vector
	bool equals(const Item&);								//���صȺ������
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
	set<int>							terSymbol;			//�ս��
	set<int>							unTerSymbol;		//���ս��
	vector < pair<int, vector<int>>>		gram;			//��ʼ��ʾ�ķ�		
	vector<Item*>						initalItems;		//��ʼ�Ļ�
	vector<Item*>						expendItems;		//��չ�ķ�
	unordered_map<int, set<int>>			firstSet;		//���㵥���ַ���First��
	CFG() {}
	CFG(set<int> terminal, set<int> unterminal, vector <pair<int, vector<int>>>g) {
		this->terSymbol = terminal;
		this->unTerSymbol = unterminal;
		this->gram = g;

	}
	void getInitItems();										//��ȡ��ʼ�ķ�
	void getLRItems();										//�����չ�ķ�
	set<int> getFirstSet(int num,set<int>);								//����ÿ���ַ���First��
	set<int> calFirstSet(vector<int>);							//�����ַ�����First��
};
class Closure
{
public:
	vector<pair<Item*, int>>family;						//��ǰ����ıհ�
	int 	initalSize;
	void buildFamilySign(Item*, int, CFG&, bool);	 	//���ݴ����������ݹ���հ�
	void buildFamily(CFG&);
	bool isInClosure(Item*, int);					//�жϵ�ǰLR(1)��Ŀ�Ƿ��ڸñհ���
	Closure(vector<pair<Item*, int>> F) {
		this->family = F;
		this->initalSize = F.size();
	}
};
void printClosure(Closure& t);
class table {
public:
	CFG											cfggram;				//�����ķ�
	vector<Closure>								cfgClosures;			//���ɱհ�
	map<int, vector<pair<int, int>>>			actionetab;				//ACTION����ʾ��ת��������ʾ��ת��һ��λ�ã�������ʾʹ���ķ����й�Լ��1W��ʾȫ��OK��
	map<int, vector<pair<int, int>>>			gototab;				//goto��������ʾ��ת��һ��λ�ã�0��ʾɶҲ���ɡ�
	void buildTable();													//����Action���goto��
	table(CFG c) {
		this->cfggram = c;
	}
};
//����հ�
void table::buildTable() {//ʹ�ÿ�����ȱ����ķ�������table
	vector<pair<Item*, int>> initClosuer = { { this->cfggram.expendItems[0],-2 } };//��ʾһ��ʼ���ķ�
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
		map<int, vector<pair<Item*, int>>> m;//��ʾ�������ɵ�NEXT�ķ�,int��ʾת��������numΪ����
		for (auto& p : tmp.family) {
			if (p.first->dotPosition == p.first->right.size() - 1) {//��ʾ���ع�Լ���ܼ���
				if (p.second == -2 && p.first->left == 1 && p.first->right[0] == bg) {//��ʾΪacc�����
					actionetab[idx].push_back({ p.second,10000 });//��ʾ��Լ�����յ�i���ķ�
				}
				else {
					actionetab[idx].push_back({ p.second,-p.first->idx });
				}
			}
			else {
				int idex = p.first->dotPosition + 1;//idex��ʾλ��
				int t = p.first->right[idex];//��ʾ.֮����ַ�
				m[t].push_back({ this->cfggram.expendItems[p.first->expidx + 1],p.second });//��ȡ����ĵ�CLOSURE
			}
		}
		for (auto&p : m) {//p.first=int,��ʾ��һ���ַ�,p.second=vector<pair<Item*,int>>��ʾת��������
			bool judge = false;
			Closure newClo(p.second);//����Ŀ����ʼ��
			newClo.buildFamily(this->cfggram);//�����µ���Ŀ��
			for (int i = 0; i < cfgClosures.size(); i++) {
				if (cfgClosures[i].family.size() == newClo.family.size()) {//��ʱ��ʾ�Ѿ�����Ŀ�������ˣ�ֻ��Ҫ�������б��.
					int j = 0;
					for (j = 0; j<newClo.family.size(); j++) {
						if (!cfgClosures[i].isInClosure(newClo.family[j].first, newClo.family[j].second)) {
							break;
						}
					}
					if (j == newClo.family.size()) {
						if (this->cfggram.terSymbol.count(p.first)) {//��ʾΪ�ս��
							actionetab[idx].push_back({ p.first,i });//��ʾ�����ƽ�
						}
						else {
							gototab[idx].push_back({ p.first,i });
						}
						judge = true;
						break;
					}
				}
			}
			if (!judge) {//û���ҵ�ƥ�����Ŀ������Ҫ�����µ���Ŀ
				dfsClosure.push(newClo);
				cfgClosures.push_back(newClo);
				if (this->cfggram.terSymbol.count(p.first)) {
					actionetab[idx].push_back({ p.first,cfgClosures.size() - 1 });//��ʾ��ʱΪ���һ��
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
	int nextWait = init->right[init->dotPosition + 1];		//��ʾdot����ĵ�һ�����ս��
	vector<int> follow;										//Ϊ���ս������ķ��ż���
	int beginPos = init->dotPosition + 2;
	for (int i = beginPos; i<init->right.size(); i++) {
		follow.push_back(init->right[i]);
	}
	follow.push_back(initNum);
	set<int>first = gram.calFirstSet(follow);//Ѱ�Һ��򼯺ϵ�First��
											 //Ѱ����dot���濪ͷ�ķ��ս�����ķ�����first�е��ķ����
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
//CFG ��ó�ʼ�ķ���
void CFG::getInitItems() {
	for (auto& p : gram) {
		Item* inital = new Item(p.first, p.second, 0, false);
		this->initalItems.push_back(inital);
	}
}
//CFG �����չ�ķ�:
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
//��ȡ��ǰ�ַ���First��
set<int> CFG::getFirstSet(int num,set<int>allnum) {
	if (!terSymbol.count(num) && !unTerSymbol.count(num)) {
		return{};
	}
	set<int>res;
	if (firstSet.count(num)) {
		return firstSet[num];
	}//���仯����
	if (terSymbol.count(num)) {
		res.insert(num);
		firstSet.insert({ num,res });//�����ս����first��
		return res;
	}
	else {
		for (auto& item : initalItems) {
			if (item->left == num) {
				int idx = 1;
				for (int i = 0; i<idx; i++) {
					if (item->right.size() == 1 && item->right[0] == -1) {
						res.insert(-1);
					}//��ʾ��ǰ�����ֻ��һ����
					else {
						if (!allnum.count(item->right[i])) {
							allnum.insert(item->right[i]);
							set<int>tmp = getFirstSet(item->right[i],allnum);
							for (int n : tmp) {
								if (n == -1) {
									idx++;//��ʾ��ǰ����º��пգ���First�����Ժ���
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
	gram.push_back({ 1001,{ 1001,1002 } });	//����ܿس���
	gram.push_back({ 1002,{ 1004 } });
	gram.push_back({ 1004,{ 1011 } });
	gram.push_back({ 1004,{ 1034 } });
	gram.push_back({ 1004,{ 1019 } });
	gram.push_back({ 1011, { 1005,1006,61,1010,62,60 } });
	gram.push_back({ 1011,{ 1005,1006,61,62,60 } });
	gram.push_back({ 1010,{ 1005 } });
	gram.push_back({ 1010,{ 1010,59,1005 } });
	gram.push_back({ 1002,{ 1003 } });	/////////////////////////////////////////������fuck gc
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
	gram.push_back({ 1016,{ 1037 } });//��ʾ�����������
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
	m.insert({ 100, "����" });
	m.insert({ 200, "������" });
	m.insert({ 1001, "����" });
	m.insert({ 1002, "�ⲿ����" });
	m.insert({ 1003, "��������" });
	m.insert({ 1004, "��������" });
	m.insert({ 1005, "������" });
	m.insert({ 1006, "������" });
	m.insert({ 1007, "��������" });
	m.insert({ 1008, "��ʶ��" });
	m.insert({ 1009, "�����Ͳ�������" });
	m.insert({ 1010, "��������" });
	m.insert({ 1011, "��������" });
	m.insert({ 1012, "ͷ�ļ�����" });
	m.insert({ 1013, "�������" });
	m.insert({ 1014, "����" });
	m.insert({ 1015, "���List" });
	m.insert({ 1016, "���" });
	m.insert({ 1017, "��������" });
	m.insert({ 1018, "�������" });
	m.insert({ 1019, "���ʽ���" });
	m.insert({ 1020, "ѡ�����" });
	m.insert({ 1021, "ѭ�����" });
	m.insert({ 1022, "��ת���" });
	m.insert({ 1023, "���ʽ" });
	m.insert({ 1024, "����ʽ" });
	m.insert({ 1025, "��ʶ����" });
	m.insert({ 1026, "�������" });
	m.insert({ 1027, "�������ʽ" });
	m.insert({ 1028, "��Ŀ������ֵ" });
	m.insert({ 1029, "��Ŀ����" });
	m.insert({ 1030, "��ֵ���" });
	m.insert({ 1031, "��ֵ����" });
	m.insert({ 1032, "�������" });
	m.insert({ 1033, "�������" });
	m.insert({ 1034, "�����������" });
	m.insert({ 1035, "��������" });
	m.insert({ 1036, "���������" });
	m.insert({ 1037, "��Ŀ����" });
	m.insert({ 1038, "��Ŀ������" });
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
}scan_buff;//��ʾΪɨ�軺�������򣬴�СΪ256

struct input_buffer//���뻺����
{
	string all;
	string next_state;
	int index;
}in_buff;
//��������
string readFileIntoString(char * filename);
string  pre_process(input_buffer&in_buff);
void    word_analysis();
bool isdigit(char c);
bool isletter(char c);
void retract();//�������һ��
bool iskeywords(string tmp);//�ж��Ƿ��ǹؼ���


							//ȫ�ֱ���

map<string, int> keywords = { { "auto",1 },{ "break",2 },{ "case",3 },{ "char",4 },{ "const",5 },{ "continue",6 },{ "default",7 },{ "do",8 },{ "double",9 },{ "else",10 },
{ "enum",11 },{ "extern",12 },{ "float",13 },{ "for",14 },{ "goto",15 },{ "if",16 },{ "int",17 },{ "long",18 },{ "register",19 },{ "return",20 },{ "short",21 },
{ "signed",22 },{ "sizeof",23 },{ "static",24 },{ "struct",25 },{ "switch",26 },{ "typeof",27 },{ "union",28 },{ "unsigned",29 },{ "void",30 },
{ "volatile",31 },{ "while",32 } };
set<char>operator_t1 = { '+','*','|','=','&','|','>','<',':' };//c,cc,c=���ֶ���
set<char>operator_t2 = { '/','^','%' };//c,c=
set<char>operator_t3 = { '~', ',', '[', ']', '{', '}', '(', ')', '.', '?',';' };//c
set<char>operator_t4 = { ':' };//c,cc
map<string, int> operators = { { "=",33 },{ "-",34 },{ "*",35 },{ "/",36 },{ "%",37 },{ "+=",38 },{ "-=",39 },{ "*=",40 },{ "/=",41 },{ "%=",42 },{ ">",43 },{ "<",44 },{ ">=",45 },{ "<=",46 },{ ">>",47 },{ "<<",48 },
{ "==",49 },{ "!=",50 },{ "&",51 },{ "&&",52 },{ "|",53 },{ "||",54 },{ "&=",55 },{ "|=",56 },{ "++",57 },{ "--",58 },{ ",",59 },{ ";",60 },{ "(",61 },{ ")",62 },
{ "[",63 },{ "]",64 },{ "{",65 },{ "}",66 },{ "?",67 },{ ":",68 },{ ".",69 },{ "<<=",70 },{ ">>=",71 },{ "^",72 },{ "^=",73 },{ "~",74 },{ "::",75 },{ "+",76 } };
map<string, int>symbol_table;//�洢�����ķ��ű�
set<string>symbols;
int begin_num = 200;
//���ļ����뵽string��
string readFileIntoString(char * filename)
{
	ifstream ifile(filename);
	//���ļ����뵽ostringstream����buf��
	ostringstream buf;
	char ch;
	while (buf&&ifile.get(ch))
		buf.put(ch);
	//������������buf�������ַ���
	return buf.str();
}


//����Ԥ����
string pre_process(input_buffer&in_buff)//���뻺����Ԥ�������ÿ�ε��ö���һ����������䵽ɨ�軺������
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
	string res;//��ʾ����������
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
			if (index<len&&in_buff.all[index] == '/')//����//��ע�ͣ������Ƶ���ֱ����ȡ��'\n'
			{
				index++;
				while (index<len&&in_buff.all[index] != '\n')
					index++;
				index++;
			}//�����������
			else if (index<len&&in_buff.all[index] == '*')//����/*�����
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
pair<string, int> token()//����һ�����ʴ���
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
		if (getch() == '.')//���ָ����������
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
				return{ res,100 };//��ʾ����������
		}
		else
			return{ res,100 };//��ʾ������
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
				if (getch() == '.')//���ָ����������
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
						return{ res,100 };//��ʾ����������
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
						return{ res,100 };//��ʾ����������
				}
				else
					return{ res,100 };//��ʾ������
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
	else if (getch() == '\'')//��ʾchar����
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
void word_analysis()//���������������зַ���
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
	in_buff.all = readFileIntoString(filename);//���뻺���������
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
//���������ɨ�軺����Ϊ��������һ�δʷ�����
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
	status.push_back(0);							//��ʶ״̬0
	signs.push_back(-2);							//һ��ʼpush��ȥ
	int idx = 0;									//traverse��ɨ���±�
	string work;
	while (idx !=traverse.size()) {
		tablePrint(status, signs, idx, work, traverse, initial);
		work = "";
		int nextVal = traverse[idx];
		int nextStatu = findAction(status.back(),nextVal, actionetab);
		if (nextStatu != -10000) {				//���Խ����ƽ�
			if (nextStatu > 0&&nextStatu!=10000) {
				status.push_back(nextStatu);
				signs.push_back(nextVal);
				work = 's' + to_string(nextStatu);
				idx++;
			}
			else if(nextStatu<0){
				int agg = abs(nextStatu);				//��ʾ��Լ�����
				int s = gram[agg].second.size(),i=0;	//��Ҫ��Լ���ַ��ĸ���
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
			cout << "WOC ������";
			return;
		}
	}
}
void printNode(int num,pair<int, vector<int>>& p) {//num��ʾ�ո�ĸ���
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
		int idx = course.back();//idx��ʾ�õڼ�������ʽ���й�Լ
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
	vector<int>		traverse;//���봮
	vector<int>		status;//״̬
	vector<int>		signs;//���Ŵ�
	/*�����ķ��Լ�ACTION GOTO ��*/
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
	//printTree();//���ݿ�ʼ�ķ���������
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
	cout << "ACTION��" << endl;
	for (auto p : t.actionetab) {
		cout << "״̬" << p.first << "		";
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
	cout << "GOTO��" << endl;
	for (auto p : t.gototab) {
		cout << "״̬" << p.first << "		";
		for (auto a : p.second) {
			cout << m[a.first] << "		";
			cout << abs(a.second);
		}
		cout << endl;
	}*/
	getchar();
}