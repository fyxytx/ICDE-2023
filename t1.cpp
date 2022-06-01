#include <omp.h>
#include <time.h>
#include <iostream>
#include <stack>
#include <algorithm>
#include <fstream>
#include <stdlib.h>
#include <string.h>
#include <utility>
#include <set>
#include <vector>
#include <queue>
#include <map>
#include <limits>
#include <numeric>
#include <unordered_map>
#include <bitset>

#define MAXINT ((unsigned) 4294967295)


using namespace std;

#define BUCKET_ID(i, j, l) ((i)*(l) + (j))

unsigned totalV=0, place=0;
set<unsigned> elem;
vector<vector<unsigned> > con, con_R, MFlag_Left, MFlag_Right;
vector<unsigned> disL_, disR_, v2p, active_L, active_R; // 璁板綍璺濈src鍜宒st鐨勫彲鑳借窛绂


vector<vector<unsigned> > Middle_List, Extra_List;

vector<vector<long long> > v2space, v2space_Reverse;
vector<unsigned> s, flag, bar, diss;
vector<set<pair<unsigned, unsigned> > > REdges;
vector<vector<unsigned> > Cnts;
map<unsigned, set<unsigned> > Pm;

// ==== SIGMOD ===
vector<unsigned> stack1_;
long long count_ = 0, target_number_results_ = 1000, active_nums=0;
bool g_exit = false;

long long totalPath = 0, MaxPaths = 1;

struct peng{
	vector<unsigned> p;
	peng(){
		p.resize(0);
	}
	peng(unsigned a){
		p.push_back(a);
	}
	peng(vector<unsigned> a){
		p.swap(a);
	}
	bool operator < (const peng& a) const{
		if ( p.size() < a.p.size())
			return true;
		else
			return false;
	}
};


unsigned *stack_;
unsigned *visited_;

/**
 * Bipartite graph index-based method.
 */
pair<unsigned, unsigned>* distance_;
unsigned* updated_values_;
unsigned* bucket_degree_sum_;

unsigned *buckets_offset_;
unsigned *buckets_;

map<unsigned, unsigned> single_bigraph_;
unsigned *single_bigraph_offset_;
unsigned *single_bigraph_adj_;

map<unsigned, unsigned> single_reverse_bigraph_;
unsigned *single_reverse_bigraph_offset_;
unsigned *single_reverse_bigraph_adj_;

unsigned min_cut_position_;
unsigned long long estimated_left_relation_size_;
unsigned long long estimated_right_relation_size_;
unsigned long long estimated_result_count_;

unsigned *left_relation_;
unsigned long long left_relation_size_;
unsigned *left_cursor_;
unsigned *left_partial_begin_;
unsigned *left_partial_end_;
unsigned left_part_length_;
unsigned *right_relation_;
unsigned long long right_relation_size_;
unsigned *right_cursor_;
unsigned right_part_length_;
unsigned *right_partial_begin_;
unsigned *right_partial_end_;
map<unsigned, pair<unsigned*, unsigned> > index_table_;
unsigned long long preliminary_estimated_result_count_;
unsigned long long full_fledged_estimated_result_count_;
unsigned long long estimated_dfs_cost_;
unsigned long long estimated_join_cost_;
unsigned long long preliminary_selection_;
unsigned long long full_fledged_selection_;

unsigned MAXDIS, MAXMOV, MASK;



vector<int> vert2place, distance1;
vector<unsigned> src_dis, dst_dis; // 璁板綍src(dst)鍜岃竟鐣岀偣涔嬮棿鐨勮窛绂伙紝
//map<unsigned, vector<unsigned> > que_total;
vector<vector<unsigned> > Paths, Paths_Reverse;
vector<vector<unsigned> > que_total;
vector<long long> path_src, path_dst;

int aplace, bplace, global_fff = 0;

struct pth{
	vector<unsigned> p;

	pth(){
		p.resize(0);
	}

	pth(unsigned a){
		p.push_back(a);
	}

	pth(vector<unsigned>& a){
		p = a;
	}

	bool operator < (const pth& a) const{
		if (p.size() < a.p.size())
			return true;
		else
			return false;
	}

	void clear(){
		p.clear();
	}

	void resize(int n){
		p.resize(n);
	}

	void swap(){
		vector<unsigned>().swap(p);
	}
};

unsigned numV, khop, src, dst;
double t111;
unsigned Lmax, Rmax; // 宸 =鍙  or 宸 =鍙 +1
int threads;
vector<vector<vector<pth> > > Lpaths, Rpaths;
// MaxL, MaxR 鐢ㄦ潵璁板綍large-scale鍥句腑鐨勬儏鍐碉紝涓昏闃叉鍐呭瓨婧㈠嚭
vector<long long> maxL, maxR, MaxL, MaxR;

struct midd{
	int id;
	int LNow;
	int LBound;
	int RNow;
	int RBound;

	midd(){
		id = -1, LNow = -1, LBound = -1,
				 RNow = -1, RBound = -1;
	}

	midd(int id1, int LNow1, int LBound1,
			      int RNow1, int RBound1){
		id = id1,
		LNow = LNow1,
		LBound = LBound1,
		RNow = RNow1,
		RBound = RBound1;
	}
};

struct midd2{
	vector<unsigned> lp, rp;

	midd2(){
		lp.resize(0);
		rp.resize(0);
	}

	midd2(unsigned n1, unsigned n2){
		lp.push_back(n1);
		rp.push_back(n2);
	}

	midd2(vector<unsigned>& n1, vector<unsigned>& n2){
		lp.insert(lp.end(), n1.begin(), n1.end());
		rp.insert(rp.end(), n2.begin(), n2.end());
	}

	void pushL(unsigned n){
		lp.push_back(n);
	}

	void pushR(unsigned n){
		rp.push_back(n);
	}



	void swapL(vector<unsigned>& lp1){
		lp.swap(lp1);
	}

	void swapR(vector<unsigned>& rp1){
		rp.swap(rp1);
	}


};

vector<midd2> v2Middle, v2Decompose, v2De;
vector<vector<unsigned> > Elems, Flag_;


// ==============================
// ==============================

vector<vector<unsigned> > s_thread, flag_thread;
vector<vector<vector<unsigned> > > Pth_thread, Pth_R_thread;
vector<unordered_map<int, vector<vector<unsigned> > > > P_thread, P_R_thread;
vector<vector<midd2> > v2M_P;

struct PTnode{
	int id;    // 瀵瑰簲鍥句腑鐨刬d
	// OPEN 1, CLOSED 2, POTENTIAL 3, POSTPONE 4, NULL 5
	int state; // 鍏辨湁5涓暟
	unordered_map<int, int > pt, dis; // pruning thresholds for vertices
	int parent; // 鍦ㄨ矾寰勪腑鐨勪綅缃
	int child; // 瀛╁瓙鑺傜偣鏁伴噺
	int level; // 鍦ㄦ爲涓殑灞

	PTnode(){
		id = -1, state = -1; parent = -1; child = -1; level = -1;
	}

	PTnode(int id1, int sta, int pla, int chd, int lv){
		id = id1, state = sta; parent = pla; child = chd; level = lv;
	}
};

vector<vector<PTnode> > Branches; // 鍒涘缓鐨勫垎鏀
int treeid = 0, cnt = 0;
vector<int> treelist;
int delta = 50; // 婵 娲荤殑涓婇檺鍊
//unordered_map<int, PTnode> TreeMap;
int maxlevel = 0;

//  杈撳叆鍒濆鍖栧嚱鏁
void initial2(unsigned& numV, int flag1){ // 鍒濆鍖栧弬鏁
	con.resize(numV);
	int n = 0, m = 0;
	vector<pair<int, int> > v2degree;

	string s, name = "/home/hnu/Disk0/zyy_dataset/it2004/it2004.txt";
//	string s, name = "facebook/graph2.txt";
	cout<<name<<endl;
	const char *file = name.c_str();
	ifstream infile;
	infile.open(file);
	if(!infile.is_open()){
		cout<<"No such file!"<<endl;
		exit(-1);
	}

	long xx = 0;

	while(getline(infile,s)){
		char* strc = new char[strlen(s.c_str())+1];
		strcpy(strc, s.c_str());
		int Vid_A, Vid_B, dis;
		char *s1 = strtok(strc," ");
		unsigned n1=0; Vid_A = atoi(s1);

		while(s1=strtok(NULL," ")){
			n1++;
			switch(n1){
				case 1: Vid_B = atoi(s1); break;
			}

			if (n1==1){
				n1 = 0;
				con[Vid_A].push_back(Vid_B);
				con[Vid_B].push_back(Vid_A);
				n = max(max(n, Vid_A+1), Vid_B+1);
				m += 1;
			}
		}
	}

	numV = n;
	for( int i = 0; i < numV; ++i )
		v2degree.push_back(make_pair(con[i].size(), i));

	sort(v2degree.rbegin(), v2degree.rend());

	src = v2degree[aplace].second;
	dst = v2degree[bplace].second;

//	src = 0;
//	dst = 6;
//	khop = 4;


	cout<<"src: "<<src<<"  dst: "<<dst<<endl;
	con.resize(numV);
	flag.resize(numV);
	bar.resize(numV);

	cout<<"Node: "<<n<<"  Edge: "<<m<<endl;
}

void initial1(unsigned& numV, int flag1){ // 初始化参数
	con.resize(numV);
	int n = 0, m = 0;
	vector<pair<int, int> > v2degree;

	string s, name = "/home/hnu/Disk0/zyy_dataset/pokec/pokec.txt";
//	string s, name = "facebook/graph2.txt";
	cout<<name<<endl;
	const char *file = name.c_str();
	ifstream infile;
	infile.open(file);
	if(!infile.is_open()){
		cout<<"No such file!"<<endl;
		exit(-1);
	}

	long xx = 0;

	while(getline(infile,s)){
		char* strc = new char[strlen(s.c_str())+1];
		strcpy(strc, s.c_str());
		int Vid_A, Vid_B, dis;
		char *s1 = strtok(strc," ");
		unsigned n1=0; Vid_A = atoi(s1);

		while(s1=strtok(NULL," ")){
			n1++;
			switch(n1){
				case 1: Vid_B = atoi(s1); break;
			}

			if (n1==1){
				if ( xx % 10 <= 5){
					n1 = 0;
					con[Vid_A].push_back(Vid_B);
					con[Vid_B].push_back(Vid_A);
					n = max(max(n, Vid_A+1), Vid_B+1);
					m += 1;
				}
			}
		}

		xx += 1;
	}

	numV = n;
	for( int i = 0; i < numV; ++i )
		v2degree.push_back(make_pair(con[i].size(), i));

	sort(v2degree.rbegin(), v2degree.rend());

	src = v2degree[aplace].second;
	dst = v2degree[bplace].second;


//	src = 24995710;
//	dst = 37794987;
//	khop = 8;



	con.resize(numV+1);
	flag.resize(numV+1);
	bar.resize(numV+1);

	cout<<"Node: "<<n<<"  Edge: "<<m<<endl;
}


void printArray(vector<unsigned>& arrays){
	for (int i=0; i<arrays.size(); ++i)
		cout<<arrays[i]<<" ";
	cout<<endl;
}


void printArray2(vector<unsigned>& arrays){
	for (int i=0; i<arrays.size(); ++i)
		cout<<arrays[arrays.size()-1-i]<<" ";
}



// VLDB 2019 Peng

void UpdateBarrier(unsigned u, unsigned l){
	if (bar[u] > l){
		bar[u] = l;
		for (unsigned ii=0; ii<(unsigned)con[u].size(); ii++){
			unsigned v = con[u][ii];
			if ( flag[v] == 1 )
				continue;

			UpdateBarrier(v, l+1);
		}
	}
};


int Peng_DFS(int u, int dst, int khop){
	int num = khop+1;
	s.push_back(u);
	flag[u] = 1; // 琛ㄧず椤剁偣瀛樺湪浜庣幇鏈夐亶鍘嗚矾寰勯噷闈

	if (u == dst){
		totalPath += 1;
		s.pop_back();
		flag[u] = 0;

		return 0;

	} else if( s.size() < khop+1 ){ // 褰撳墠璺虫暟鏈揪鍒颁笂闄

		for (int ii=0; ii<(int)con[u].size(); ii++){

			int v = con[u][ii];

			if ( flag[v] == 1) // 绠 鍗曡矾寰勪腑椤剁偣鍏锋湁鍞竴鎬
				continue;

			if (s.size() - 1 +  bar[v] <= khop){
				int num_ = Peng_DFS(v, dst, khop);
				if (num_ != khop + 1)
					num = min(num, num_+1);
			}
		}
	}

	if (num == khop+1)
		bar[u] = khop - s.size() + 2;
	else
		UpdateBarrier(u, num);

	s.pop_back();
	flag[u] = 0;

	return num;
}

int Peng_DFS_Join(int u, int dst, int khop, map<unsigned, vector<peng> >& Paths){


	int num = khop+1;
	s.push_back(u);
	flag[u] = 1; // 琛ㄧず椤剁偣瀛樺湪浜庣幇鏈夐亶鍘嗚矾寰勯噷闈

	if (u == dst){

		totalPath += 1;
		s.pop_back();
		flag[u] = 0;
		peng pp(s);
		Paths[s[s.size()-1]].push_back(pp);

		return 0;

	}else if( s.size() < khop+1 ){ // 褰撳墠璺虫暟鏈揪鍒颁笂闄

		for (int ii=0; ii<(int)con[u].size(); ii++){

			int v = con[u][ii];

			if ( flag[v] == 1) // 绠 鍗曡矾寰勪腑椤剁偣鍏锋湁鍞竴鎬
				continue;

			if (s.size() - 1 +  bar[v] <= khop){
				int num_ = Peng_DFS_Join(v, dst, khop, Paths);
				if (num_ != khop + 1)
					num = min(num, num_+1);
			}
		}
	}

	if (num == khop+1)
		bar[u] = khop - s.size() + 2;
	else
		UpdateBarrier(u, num);

	s.pop_back();
	flag[u] = 0;

	return num;
}


void MiddleVFind(unsigned src, unsigned dst, unsigned khop, unsigned numV){
    unsigned q1 = khop/2, q2 = khop%2, i=0;
    unsigned dt = q1+q2, st = q1;
    if (q2 > 0) st = q1+1;
    distance_ = new pair<unsigned, unsigned> [numV];

	set<unsigned> L, R;
	set<unsigned>::iterator it;
	L.insert(src), R.insert(dst);
	distance_[src].first = 1, distance_[dst].second = 1;

	while(i <= st){
		set<unsigned> L_, R_;

		for (it=L.begin(); it!=L.end(); ++it)
			for(unsigned j=0; j<(unsigned)con[*it].size(); j++){
				unsigned vv = con[*it][j];
				if (distance_[vv].first == 1) continue;

				L_.insert(vv); distance_[vv].first=1;
				if (R.find(vv)!=R.end())
					Pm[2*i-1].insert(vv);
			}

		if (i == dt) break;

		for (it=R.begin(); it!=R.end(); ++it)
			for(unsigned j=0; j<(unsigned)con[*it].size(); j++){
				unsigned vv = con[*it][j];
				if (distance_[vv].second == 1) continue;

				R_.insert(con[*it][j]); distance_[vv].second=1;
				if (L_.find(con[*it][j]) != L_.end())
					Pm[2*i].insert(con[*it][j]);
			}

		i++;
		L = L_, R = R_;
	}

	int nn = 0;
	for (unsigned i=0; i<khop; i++){
		if (Pm.find(i)==Pm.end()) continue;

		for (it=Pm[i].begin(); it!=Pm[i].end(); ++it)
			nn += 1;
	}
	cout<<"Middle: "<<nn<<endl;
};


void Peng_Join(unsigned src, unsigned dst, unsigned khop, unsigned numV){
	cout<<"Peng Join:"<<endl;

    unsigned q1 = khop/2, q2 = khop%2;
    unsigned dt = q1+q2, st = q1;

	set<unsigned>::iterator it;
	MiddleVFind(src, dst, khop, numV); // 纭Pm鐨勫厓绱

	// 閮藉姞涓 涓熬宸
	set<unsigned> midd;
	for (unsigned i=0; i<khop; i++){
		for (it=Pm[i].begin(); it!=Pm[i].end(); ++it){
			con[*it].push_back(numV);
			con[numV].push_back(*it);
			midd.insert(*it);
		}
	}

	map<unsigned, vector<peng> > PathL, PathR;
	Peng_DFS_Join(src, numV, dt+1, PathL);
	Peng_DFS_Join(dst, numV, st+1, PathR);

	totalPath = 0;
	vector<unsigned> elems(numV, 0);
//	cout<<"L size: "<<PathL.size()<<"   R size: "<<PathR.size()<<endl;

	// 鍚堝苟绋嬪簭锛屾妸瀵瑰彛璺緞鍚堝苟璧锋潵
	for(set<unsigned>::iterator it=midd.begin(); it!=midd.end(); ++it){
		if (PathL.find(*it) == PathL.end() or PathR.find(*it) == PathR.end())
			continue;

		vector<peng>& LP = PathL[*it];
		vector<peng>& RP = PathR[*it];

		sort(LP.begin(), LP.end());
		sort(RP.begin(), RP.end());

		int Lsize = LP.size(), Rsize = RP.size();

//		cout<<"L: "<<Lsize<<"  R: "<<Rsize<<endl;
//		cout<<"  **  "<<LP[0].p.size()<<"   "<<RP[0].p.size()<<endl;

		for (int i=0; i<Lsize; ++i){
			peng& L1 = LP[i];

//			cout<<" L: ";
//			for (int k=0; k<L1.p.size(); ++k)
//				cout<<L1.p[k]<<"  ";
//			cout<<endl;

			for(int j=1; j<L1.p.size(); ++j){
				elems[L1.p[j]] = 1;
			}

			for (int ii=0; ii<Rsize; ++ii){
				peng& R1 = RP[ii];
//				cout<<"    R: ";
//				for (int k=0; k<R1.p.size(); ++k)
//					cout<<R1.p[k]<<"  ";
//				cout<<endl;
				if (L1.p.size() < R1.p.size())
					break;

				if (L1.p.size() == R1.p.size() ||
						L1.p.size() == R1.p.size()+1){

					int ff = 1;
					for (int jj=0; jj<R1.p.size()-1; ++jj){
						if(elems[R1.p[jj]] == 1){
							ff = 0; // 瀛樺湪閲嶅鍏冪礌
							break;
						}
					}

					if (ff == 1){

						totalPath += 1;
					}
				}
			}

			for(int j=1; j<L1.p.size(); ++j){
				elems[L1.p[j]] = 0;
			}
		}


	}

	cout<<"Paths: "<<totalPath<<endl;
};


// 2021 Sigmod Sun

void BuildIndex(unsigned src, unsigned dst, unsigned numV, unsigned khop){

    visited_ = new unsigned [numV];
    memset(visited_, 0, sizeof(unsigned)*numV);

    updated_values_ = new unsigned [numV];
    memset(updated_values_, 0, sizeof(unsigned)*numV);

    distance_ = new pair<unsigned, unsigned> [numV];
	memset(distance_, 0, sizeof(pair<unsigned, unsigned>)*numV);

	for (unsigned i=0; i<numV; i++){
		distance_[i].first = khop+1; distance_[i].second = khop+1;
	}

	unsigned long long num_edges = 0;
	unsigned updated_count = 0;
    visited_[src] = 1, visited_[dst] = 1;
    updated_values_[updated_count++] = src;
    updated_values_[updated_count++] = dst;

    int vvalue = 0;
    queue<unsigned> q;
    q.push(src);
    distance_[src].first = 0;

    while(!q.empty()){
    	unsigned v = q.front();
    	q.pop();

    	if (distance_[v].first < khop - 1){
    		unsigned next_distance = distance_[v].first + 1;

            for (unsigned ii = 0; ii < (unsigned) con[v].size(); ++ii) {
            	unsigned vv = con[v][ii];

            	if (visited_[vv] == 0){
                    visited_[vv] = 1;
                    distance_[vv].first = next_distance;
                    updated_values_[updated_count++] = vv;
                    q.push(vv);
            	}
            }
    	}
    }


    vector<vector<unsigned> > temp_buckets((khop + 1) * (khop + 1));
    if (numV / updated_count > 64 * 32) {
        for (unsigned i = 0; i < updated_count; ++i) {
            visited_[updated_values_[i]] = 0; // 閲嶇疆
        }
    }
    else {
        memset(visited_, 0, sizeof(unsigned) * numV);
    }


    q.push(dst);
    visited_[src] = 1;
    visited_[dst] = 1;
    distance_[dst].second = 0;
    unsigned active_vertices_count = 0;

    while (!q.empty()){
        unsigned v = q.front();
        q.pop();

        if (distance_[v].second < khop - 1){
        	unsigned next_distance = distance_[v].second + 1;

        	for (unsigned ii = 0; ii < (unsigned)con[v].size(); ++ii){
            	unsigned vv = con[v][ii];

            	if (visited_[vv]==0 && distance_[vv].first + next_distance <= khop){
                    visited_[vv] = 1;
                    distance_[vv].second = next_distance;
                    q.push(vv);

                    vvalue += 1;
                    active_vertices_count += 1;
                    unsigned bucket_id = BUCKET_ID(distance_[vv].first, distance_[vv].second, khop + 1); // 璁捐涓 涓搴旂殑buck_id

                    temp_buckets[bucket_id].push_back(vv);
            	}
        	}
        }
    }

//    cout<<"Middle:  "<<vvalue<<endl;
    active_vertices_count += 1;

    // 杩涗竴姝ユ瀯寤篿ndex
    buckets_=(unsigned*)malloc(sizeof(unsigned) * active_vertices_count);
    buckets_offset_ = (unsigned*)malloc(sizeof(unsigned) * ((khop + 1) * (khop + 1) + 1));
    buckets_[0] = src;

    unsigned offset = 1; // 0浣嶇疆宸茬粡琚玸rc_鍗犳嵁浜
	for (unsigned i = 0; i < khop + 1; ++i) {
		for (unsigned j = 0; j < khop + 1; ++j) {
			unsigned bucket_id = BUCKET_ID(i, j, khop + 1);
			buckets_offset_[bucket_id] = offset; // 璁板綍璧峰浣嶇疆
			// 鎷疯礉鏁版嵁, buckets_鏋勬垚鐨勬槸Neighbors鍒椼
			memcpy(buckets_ + offset, temp_buckets[bucket_id].data(), sizeof(unsigned) * temp_buckets[bucket_id].size());
			offset += temp_buckets[bucket_id].size();

			temp_buckets[bucket_id].clear();
		}
	}
    buckets_offset_[(khop + 1) * (khop + 1)] = offset;



    vector<unsigned> temp_bigraph_adj;
    temp_bigraph_adj.reserve(1024);

    vector<vector<unsigned> > temp_adj(khop);
    single_bigraph_offset_ = (unsigned*)malloc(sizeof(unsigned) * khop * (active_vertices_count + 1));
    memset(single_bigraph_offset_, 0, sizeof(unsigned) * khop * (active_vertices_count + 1));


    unsigned cur_bucket_id = 0;
    unsigned cur_bucket_offset = buckets_offset_[cur_bucket_id + 1];
    unsigned cur_bucket_max_degree_offset = cur_bucket_id * (khop + 1);

    bucket_degree_sum_ = (unsigned*)malloc(sizeof(unsigned) * (khop + 1) * (khop + 1) * (khop + 1));


    for (unsigned i = 0; i < active_vertices_count; ++i) {
    	unsigned v = buckets_[i];

        if (i != 0) {
            while (i >= cur_bucket_offset) {
                cur_bucket_id += 1;
                cur_bucket_max_degree_offset = cur_bucket_id * (khop + 1);
                cur_bucket_offset = buckets_offset_[cur_bucket_id + 1];
            }
        }

		// Find the bucket id.
		for (unsigned j = 0; j < (unsigned)con[v].size(); ++j) {
			unsigned vv = con[v][j];

			if (vv == dst) {
				temp_adj[0].push_back(vv);
			}
			else if (visited_[vv] == 1 && distance_[vv].second < khop) {
				temp_adj[distance_[vv].second].push_back(vv);
			}
		}

		unsigned temp_offset = i * khop, local_degree = 0;

		for (unsigned j = 0; j < khop; ++j) {

			single_bigraph_offset_[temp_offset + j] = temp_bigraph_adj.size();
			temp_bigraph_adj.insert(temp_bigraph_adj.end(), temp_adj[j].begin(), temp_adj[j].end());
            local_degree += temp_adj[j].size();
			temp_adj[j].clear();

            if (i != 0) {
                bucket_degree_sum_[cur_bucket_max_degree_offset + j] += local_degree;
            }
            else {
                bucket_degree_sum_[j] = local_degree;
            }
		}

		single_bigraph_offset_[temp_offset + khop] = temp_bigraph_adj.size();
		single_bigraph_[v] = temp_offset;
	}

    unsigned temp_res_for_test1 = temp_bigraph_adj.size();
	num_edges += temp_res_for_test1;
	single_bigraph_adj_ = (unsigned*)malloc(sizeof(unsigned) * temp_bigraph_adj.size());
	memcpy(single_bigraph_adj_, temp_bigraph_adj.data(), sizeof(unsigned) * temp_bigraph_adj.size());
	temp_bigraph_adj.clear();


	// Construct the backward bipartite graph.
	single_reverse_bigraph_offset_ = (unsigned*)malloc(sizeof(unsigned) * khop * (active_vertices_count + 1));
	memset(single_reverse_bigraph_offset_, 0, sizeof(unsigned) * khop * (active_vertices_count + 1));




	buckets_[0] = dst;
	for (unsigned i = 0; i < active_vertices_count; ++i) {
		unsigned v = buckets_[i];

		for (unsigned j = 0; j < (unsigned)con[v].size(); ++j) {
			unsigned vv = con[v][j];

			if (vv == src) {
				temp_adj[0].push_back(vv);
			}
			else if (visited_[vv] && distance_[vv].first < khop) {
				temp_adj[distance_[vv].first].push_back(vv);
			}
		}

		unsigned temp_offset = i * khop;
		for (unsigned j = 0; j < khop; ++j) {
			single_reverse_bigraph_offset_[temp_offset + j] = temp_bigraph_adj.size();
			temp_bigraph_adj.insert(temp_bigraph_adj.end(), temp_adj[j].begin(), temp_adj[j].end());
			temp_adj[j].clear();
		}

		single_reverse_bigraph_offset_[temp_offset + khop] = temp_bigraph_adj.size();
		single_reverse_bigraph_[v] = temp_offset;
	}


	unsigned temp_res_for_test2 = temp_bigraph_adj.size();
	//assert(temp_res_for_test1 == temp_res_for_test2);
	num_edges += temp_res_for_test2;
	single_reverse_bigraph_adj_ = (unsigned*)malloc(sizeof(unsigned) * temp_bigraph_adj.size());
	memcpy(single_reverse_bigraph_adj_, temp_bigraph_adj.data(), sizeof(unsigned) * temp_bigraph_adj.size());

	memset(visited_, 0, sizeof(unsigned) * numV);
	memset((unsigned*)distance_, khop + 1, sizeof(std::pair<unsigned, unsigned>) * numV);

};



void dfs_on_bigraph(unsigned u, unsigned dst, unsigned k, unsigned khop){
	stack1_.push_back(u);
	visited_[u] = 1;

	// 纭u鐨勯偦灞呯偣
	unsigned neighbor_offset = single_bigraph_[u];
	// u鐨勯偦灞呯偣鐨  鍒濆浣嶇疆
	unsigned start = single_bigraph_offset_[neighbor_offset];
	unsigned budget = khop - k - 1;
	// 纭u鏈夊灏戦偦灞呯偣鍙互琚 夋嫨
	unsigned end = single_bigraph_offset_[neighbor_offset + budget + 1];

	for (unsigned i = start; i < end; ++i){
        if (g_exit || count_ >= target_number_results_)
        	goto EXIT;

		unsigned v = single_bigraph_adj_[i];

		if (v == dst){
			totalPath += 1;
//			if (totalPath % 1000000000 == 0)
//				cout<<"     **:  "<<totalPath<<"  time: "<<omp_get_wtime()-t111<<endl;
		}else if (visited_[v] == 0){
			dfs_on_bigraph(v, dst, k+1, khop);
		}else{

		}
	}

	EXIT:
	visited_[u] = 0;
	stack1_.pop_back();
//	return ;
};


void left_dfs(unsigned u, unsigned dst, unsigned k, unsigned khop) {
    stack_[k] = u;
    visited_[u] = 1;

    // k is cost; length_constraunsigned_ - k is the remaining budget; minus 1 is the cost of moving to a out neighbor.
    unsigned budget = khop - k - 1;
    unsigned neighbor_offset = single_bigraph_[u];
    unsigned start = single_bigraph_offset_[neighbor_offset];
    unsigned end = single_bigraph_offset_[neighbor_offset + budget + 1];

//    cout<<"  y1"<<endl;

    for (unsigned i = start; i < end; ++i) {
        if (g_exit) goto EXIT;

        unsigned v = single_bigraph_adj_[i];
        if (v == dst) {
            // Emit the result.
            stack_[k + 1] = dst;
            count_ += 1;
        }
        else if (k == min_cut_position_ - 1 && !visited_[v]) {
            stack_[k + 1] = v;
            // Copy the result to the buffer.
            copy(left_partial_begin_, left_partial_end_, left_cursor_);
            left_cursor_ += left_part_length_;
            left_relation_size_ += 1;
        }
        else if (!visited_[v]) {
            left_dfs(v, dst, k + 1, khop);
        }
        else {

        }
    }

    EXIT:
    visited_[u] = 0;
}


void right_dfs(unsigned u, unsigned dst, unsigned k, unsigned khop) {
    stack_[k] = u;
    visited_[u] = 1;

    // k is cost; length_constraunsigned_ - k is the remaining budget; minus 1 is the cost of moving to a out neighbor.
    unsigned budget = khop - k - 1;
    unsigned neighbor_offset = single_bigraph_[u];
    unsigned start = single_bigraph_offset_[neighbor_offset];
    unsigned end = single_bigraph_offset_[neighbor_offset + budget + 1];

    for (unsigned i = start; i < end; ++i) {
        if (g_exit) goto EXIT;

        unsigned v = single_bigraph_adj_[i];
        if (v == dst) {
            // Emit the result.
            stack_[k + 1] = dst;
//cout<<111<<endl;
            copy(right_partial_begin_, right_partial_end_, right_cursor_);
//cout<<222<<endl;

            right_cursor_ += right_part_length_;
            right_relation_size_ += 1;
        }
        else if (k == khop - 2 && !visited_[v]) {
            stack_[k + 1] = v;
            stack_[k + 2] = dst;
            // Copy the result to the buffer.
            copy(right_partial_begin_, right_partial_end_, right_cursor_);
            right_cursor_ += right_part_length_;
            right_relation_size_ += 1;
        }
        else if (!visited_[v]) {
            right_dfs(v, dst, k + 1, khop);
        }
        else {
        }
    }

    EXIT:
    visited_[u] = 0;
}


bool preliminary_cardinality_estimator(unsigned khop) {
    // the first bucket stores src.
	preliminary_estimated_result_count_ = bucket_degree_sum_[khop - 1];
    for (unsigned i = 1; i < khop; ++i) {
        unsigned degree_sum = 1;
        unsigned vertex_sum = 1;
        for (unsigned j = 1; j <= i; ++j) {
            for (unsigned k = 1; k <= khop - i; ++k) {
            	unsigned budget = khop - i - 1;
            	unsigned cur_degree = bucket_degree_sum_[BUCKET_ID(j, k, khop + 1) * (khop + 1) + budget];
            	unsigned cur_vertex = buckets_offset_[BUCKET_ID(j, k, khop + 1) + 1] - buckets_offset_[BUCKET_ID(j, k, khop + 1)];

            	degree_sum += cur_degree;
                vertex_sum += cur_vertex;
            }
        }

        preliminary_estimated_result_count_ *= (degree_sum / vertex_sum) > 1 ? (degree_sum / vertex_sum) : 1;
    }

    return preliminary_estimated_result_count_ > 100000;
}


void single_join(unsigned dst){
	left_cursor_ = left_relation_;
	unsigned left_key_position = left_part_length_ - 1;
	for (unsigned i = 0; i < left_relation_size_; ++i) {
		// Initialize visited table.
		for (unsigned j = 0; j < left_part_length_; ++j) {
			unsigned u = left_cursor_[j];
			visited_[u] = 1;
		}

		// Join with the partitions.
		unsigned key = left_cursor_[left_key_position];
		if (index_table_.find(key)!=index_table_.end()) {
			right_cursor_ = index_table_[key].first;
			for (unsigned long long j = 0; j < index_table_[key].second; ++j) {
				if(g_exit){
					return;
				}
				for (unsigned k = 1; k < right_part_length_; ++k) {
					unsigned u = right_cursor_[k];
					if (u == dst) {
						count_ += 1;
						break;
					} else if (visited_[u]) {
						break;
					}
				}
				right_cursor_ += right_part_length_;
			}
		}

		// Clear visited table.
		for (unsigned j = 0; j < left_part_length_; ++j) {
			unsigned u = left_cursor_[j];
			visited_[u] = 0;
		}

		left_cursor_ += left_part_length_;
	}
}


void generate_single_join_plan(unsigned src, unsigned dst, unsigned numV, unsigned khop){
	unsigned num_vertices = numV;
	vector<unsigned long long> current_value(num_vertices, 0);
	vector<unsigned long long> previous_value(num_vertices, 0);

	// Estimate the number of paths to dst.
	vector<unsigned long long> num_path_to_dst(khop + 1, 0);

	for (unsigned budget = 1; budget < khop; ++budget) {
		// i is the distance to dst and j is the distance from src.
		unsigned long long global_sum = 0;
		unsigned remaining_budget = budget - 1;

		for (unsigned i = 1; i <= budget; ++i) {
			for (unsigned j = 1; j <= khop - budget; ++j) {
				unsigned bucket_id = BUCKET_ID(j, i, khop + 1);
				for (unsigned k = buckets_offset_[bucket_id]; k < buckets_offset_[bucket_id + 1]; ++k) {
					unsigned u = buckets_[k];
					// budget is i - 1.
					unsigned neighbor_offset = single_bigraph_[u];
					unsigned start = single_bigraph_offset_[neighbor_offset];
					unsigned end = single_bigraph_offset_[neighbor_offset + remaining_budget + 1];

					unsigned long long local_sum = 0;
					for (unsigned l = start; l < end; ++l) {
						unsigned v = single_bigraph_adj_[l];
						if (v == dst) {
							local_sum += 1;
						} else {
							local_sum += previous_value[v];
						}
					}
					current_value[u] = local_sum;
					global_sum += local_sum;
				}
			}
		}
		num_path_to_dst[budget] = global_sum;
		previous_value.swap(current_value);
	}
	{
		estimated_result_count_ = 0;
		unsigned neighbor_offset = single_bigraph_[src];
		unsigned start = single_bigraph_offset_[neighbor_offset];
		unsigned end = single_bigraph_offset_[neighbor_offset + khop];
		for (unsigned i = start; i < end; ++i) {
			unsigned u = single_bigraph_adj_[i];
			if (u == dst) {
				estimated_result_count_ += 1;
			} else {
				estimated_result_count_ += previous_value[u];
			}
		}
	}

	fill(previous_value.begin(), previous_value.end(), 0);
	fill(current_value.begin(), current_value.end(), 0);

	// Estimate the number of paths
	vector<unsigned long long> num_path_from_src(khop + 1, 0);
	for (unsigned budget = 1; budget < khop; ++budget) {
		// i is the distance from src and j is the distance to dst.
		unsigned long long global_sum = 0;
		unsigned remaining_budget = budget - 1;

		for (unsigned i = 1; i <= budget; ++i) {
			for (unsigned j = 1; j <= khop - budget; ++j) {
				unsigned bucket_id = BUCKET_ID(i, j, khop + 1);

				for (unsigned k = buckets_offset_[bucket_id]; k < buckets_offset_[bucket_id + 1]; ++k) {
					unsigned u = buckets_[k];
					// budget is i - 1.
					unsigned neighbor_offset = single_reverse_bigraph_[u];
					unsigned start = single_reverse_bigraph_offset_[neighbor_offset];
					unsigned end = single_reverse_bigraph_offset_[neighbor_offset + remaining_budget + 1];

					unsigned long long local_sum = 0;
					for (unsigned l = start; l < end; ++l) {
						unsigned v = single_reverse_bigraph_adj_[l];
						if (v == src) {
							local_sum += 1;
						} else {
							local_sum += previous_value[v];
						}
					}

					current_value[u] = local_sum;
					global_sum += local_sum;
				}
			}
		}
		num_path_from_src[budget] = global_sum;
		previous_value.swap(current_value);
	}

	unsigned long long min_sum = numeric_limits<unsigned long long>::max();
	for (unsigned i = 1; i < khop; ++i) {
		unsigned long long cur_sum = num_path_to_dst[i] + num_path_from_src[khop - i];
		if (cur_sum < min_sum) {
			min_sum = cur_sum;
			min_cut_position_ = khop - i;
		}
	}

	estimated_left_relation_size_ = num_path_from_src[min_cut_position_];
	estimated_right_relation_size_ = num_path_to_dst[khop - min_cut_position_];
//	cout<<"  "<<khop-min_cut_position_<<"   "<<num_path_to_dst.size()<<"   "<<num_path_to_dst[khop - min_cut_position_]<<endl;
	full_fledged_estimated_result_count_ = estimated_result_count_;

	// Estimated cost of DFS: the total number of unsignedermediate results.
	estimated_dfs_cost_ = 0;
	for (unsigned i = 1; i < khop; ++i) {
		estimated_dfs_cost_ += num_path_from_src[i];
	}

	// Materialization cost of the partial results + loop over the results. 1.05 is the penalty of checking the duplicate vertices.
	estimated_join_cost_ = estimated_left_relation_size_ + estimated_right_relation_size_ + (unsigned)(estimated_result_count_ * 1.05);

	full_fledged_selection_ = estimated_join_cost_ < estimated_dfs_cost_ ? 1 : 0;

}


void single_join_on_bigraph(unsigned src, unsigned dst, unsigned khop) {
    // Initialize.
    left_part_length_ = min_cut_position_ + 1;
    right_part_length_ = khop - min_cut_position_ + 1;
    left_relation_size_ = 0;
    right_relation_size_ = 0;
    left_partial_begin_ = stack_;
    left_partial_end_ = left_partial_begin_ + left_part_length_;
    right_partial_begin_ = stack_ + min_cut_position_;
    right_partial_end_ = right_partial_begin_ + right_part_length_;

//    cout<<left_part_length_<<"   "<<right_part_length_<<"   "<<estimated_left_relation_size_<<"   "<<estimated_right_relation_size_<<endl;
    left_relation_  = (unsigned*)malloc(sizeof(unsigned) * left_part_length_ * estimated_left_relation_size_);
    right_relation_ = (unsigned*)malloc(sizeof(unsigned) * right_part_length_ * estimated_right_relation_size_);

    // Allocate the memory for the materialization.
    left_cursor_ = left_relation_;
    left_dfs(src, dst, 0, khop);

    // Allocate the memory for the materialization.
    right_cursor_ = right_relation_;

    for (unsigned i = 1; i <= min_cut_position_; ++i) {
        for (unsigned j = 1; j <= khop - min_cut_position_; ++j) {
        	unsigned bucket_id = BUCKET_ID(i, j, khop + 1);
            for (unsigned k = buckets_offset_[bucket_id]; k < buckets_offset_[bucket_id + 1]; ++k) {
            	unsigned u = buckets_[k];
            	unsigned* cursor = right_cursor_;
//            	cout<<u<<" "<<dst<<" "<<min_cut_position_<<" "<<khop<<endl;
                right_dfs(u, dst, min_cut_position_, khop);
                unsigned long long temp_count = (right_cursor_ - cursor) / right_part_length_;
                index_table_[u] = make_pair(cursor, temp_count);
            }
        }
    }


    single_join(dst);

    free(left_relation_);
    free(right_relation_);
    index_table_.clear();
}


void Sun_DFS(unsigned src, unsigned dst, unsigned numV, unsigned khop){
	cout<<" Sun DFS:"<<endl;

//	t111 = omp_get_wtime();
	BuildIndex(src, dst, numV, khop);
	memset(visited_, 0, sizeof(unsigned)*numV);
	totalPath = 0;
	dfs_on_bigraph(src, dst, 0, khop);
	cout<<"Sun: "<<totalPath<<endl;
}


void Sun_Join(unsigned src, unsigned dst, unsigned numV, unsigned khop){
	cout<<"Sun Join:"<<endl;

	BuildIndex(src, dst, numV, khop);
    unsigned size = sizeof(unsigned) * (khop + 10);
    stack_ = (unsigned*)malloc(size);
    memset(stack_, 0, size);

	memset(visited_, 0, sizeof(unsigned)*numV);
	preliminary_cardinality_estimator(khop);
	generate_single_join_plan(src, dst, numV, khop);
	single_join_on_bigraph(src, dst, khop);
	cout<<"Paths: "<<count_<<endl;
}





// === 2022 Zeng  ===

int Queue_Select(){
	int place = -1;
	for (int it=0; it<que_total.size(); ++it){
		if (place == -1 and que_total[it].size() > 0){
			return it;
		}
	}

	return place;
}


void recompute(vector<unsigned>& arrays){
	int p=1;
	sort(arrays.begin(), arrays.end());
	for( int j = 1; j < (int) arrays.size(); ++j ){
		if( arrays[j-1] != arrays[j] )
			arrays[p++] = arrays[j];
	}
	arrays.resize(p);
}


void initial_parameters(unsigned src, unsigned dst, int Lmax, int Rmax){

	MFlag_Left.resize(active_nums,  vector<unsigned>(Lmax+1));
	MFlag_Right.resize(active_nums, vector<unsigned>(Lmax+1));
	path_src.resize(active_nums);
	path_dst.resize(active_nums);

	disL_.resize(active_nums, -1000);
	disR_.resize(active_nums, -1000);
	disL_[v2p[src]] = 0; disR_[v2p[dst]] = 0;

	for (int i=0; i<con[src].size(); ++i){
		unsigned vv = con[src][i];

		if (v2p[vv] == -1) continue;

		if (vv == dst){
			totalPath += 1;
			continue;
		}

		active_L.push_back(vv);
		disL_[v2p[vv]] = 1;
	}

	for (int i=0; i<con[dst].size(); ++i){
		unsigned vv = con[dst][i];

		if (v2p[vv] == -1 || vv == src)
			continue;

		disR_[v2p[vv]] = 1;
		active_R.push_back(vv);

		if (disL_[v2p[vv]] == 1) {// 2hop涓棿鐐
			totalPath += 1;
			path_src[v2p[vv]] += 1;
			path_dst[v2p[vv]] += 1;
		}
	}
}


void AddMiddle(){
	vector<unsigned> elem_(active_nums);

	for (int ii=0; ii<Paths_Reverse.size(); ++ii){
		vector<unsigned>& pl = Paths_Reverse[ii];

		for (int k=1; k<pl.size(); ++k){
			elem_[v2p[ pl[k] ]] = 1;
		}

		for (int jj=0; jj<Paths.size(); ++jj){
			vector<unsigned>& pr = Paths[jj];

			if (pr.size() == 1 || pl.size() == 1){ // 鐩存帴鍖归厤
				v2Middle.push_back(midd2(pl, pr));
			}else{
				int ff = 0;
				for (int k=1; k<pr.size(); ++k){
					if (elem_[v2p[ pr[k] ]] == 1){
						ff = 1; break;
					}
				}
				if (ff == 0){
					v2Middle.push_back(midd2(pl, pr));
				}
			}
		}

		for (int k=1; k<pl.size(); ++k)
			elem_[v2p[ pl[k] ]] = 0;
	}
}


void AddMiddle_parallel(int pid){

	vector<unsigned> elem_(active_nums);

	for (int ii=0; ii<Pth_R_thread[pid].size(); ++ii){
		vector<unsigned>& pl = Pth_R_thread[pid][ii];

		for (int k=1; k<pl.size(); ++k){
			elem_[v2p[ pl[k] ]] = 1;
		}

		for (int jj=0; jj<Pth_thread[pid].size(); ++jj){
			vector<unsigned>& pr = Pth_thread[pid][jj];

			if (pr.size() == 1 || pl.size() == 1){ // 鐩存帴鍖归厤
				v2M_P[pid].push_back(midd2(pl, pr));
			}else{
				int ff = 0;
				for (int k=1; k<pr.size(); ++k){
					if (elem_[v2p[ pr[k] ]] == 1){
						ff = 1; break;
					}
				}
				if (ff == 0){
					v2M_P[pid].push_back(midd2(pl, pr));
				}
			}
		}

		for (int k=1; k<pl.size(); ++k)
			elem_[v2p[ pl[k] ]] = 0;
	}
}


void BuildIndex2(int src, int dst, int numV, int khop){ // 鐩存帴鍩轰簬src_dis鍜宒st_dis杩涜鏇存柊銆
	distance_ = new pair<unsigned, unsigned> [numV];
	flag.resize(numV);
	v2p.resize(numV, -1);
	que_total.resize(khop+1); con_R.resize(numV);

	active_nums = 0;

	for (int i=0; i<numV; i++){
		distance_[i].first  = unsigned(khop+1);
		distance_[i].second = unsigned(khop+1);
	}

	que_total[0].push_back(src);

	while (1){
		int diss = Queue_Select();
		if (diss == -1)
			break;

		vector<unsigned>& q = que_total[unsigned(diss)];

		for (int i=0; i < (int)q.size(); ++i){
			int vp = q[i];

			if (flag[vp] == 1) continue; // 宸茬粡閬嶅巻杩

			flag[vp] = 1, distance_[vp].first = diss;

			if (diss == khop or vp == dst)
				continue;

			for (int ii=0; ii<(int)con[vp].size(); ++ii){
				unsigned vv = con[vp][ii];
				int dis_ = diss + 1;

				if (flag[vv] == 0 and dis_ <= khop){
					que_total[dis_].push_back(vv);
				}
			}
		}

		que_total[diss].clear();
	}

	flag.clear(); flag.resize(numV);
	que_total[0].push_back(dst);

	while (1){
		int diss = Queue_Select();
		if (diss == -1)
			break;

		vector<unsigned>& q = que_total[unsigned(diss)];

		for (int i=0; i<(int)q.size(); ++i){

			int vp = q[i];

			if (flag[vp] == 1)
				continue; // 宸茬粡閬嶅巻杩

			flag[vp] = 1, distance_[vp].second = diss;

			if (diss > khop-1 or vp == src) continue;

			for (int ii=0; ii<(int)con[vp].size(); ++ii){
				unsigned vv = con[vp][ii];
				unsigned dis_ = diss + 1;

				if (flag[vv] == 0 and dis_+distance_[vv].first <= khop){
					que_total[dis_].push_back(vv);
				}
			}
		}

		que_total[diss].clear();
	}

	flag.clear(); flag.resize(numV);

	for (int i=0; i<numV; i++){
		if(distance_[i].first + distance_[i].second <= khop){

			v2p[i] = active_nums; // id瀵瑰簲
			active_nums += 1;
			vector<pair<unsigned, unsigned> > elems, elems_R;
			vector<unsigned>& local = con[i];

			for (int j=0; j<local.size(); ++j){
				if (distance_[local[j]].second < khop+1)
					elems.push_back(make_pair(distance_[local[j]].second, local[j]));

				if (distance_[local[j]].first < khop+1)
					elems_R.push_back(make_pair(distance_[local[j]].first, local[j]));
			}

			sort(elems.begin(), elems.end());
			sort(elems_R.begin(), elems_R.end());

			vector<unsigned>().swap(local);

			for(int k=0; k<elems.size(); ++k){
				local.push_back(elems[k].second);
				con_R[i].push_back(elems_R[k].second);
			}
		}
	}

	cout<<"active: "<<active_nums<<endl;
}


void Search_Space(int src, int dst, int numV, int khop){
	// 鍏辨湁active_nums涓紝姣忎釜鍏冪礌閮藉瓨鍌 0-khop鐨勮矾寰勬暟
	v2space.resize(active_nums, vector<long long>(khop+1));
	v2space[v2p[dst]][0] = 1; // 鍙湁dst鑷韩

	for (int i=0; i<(int)con[dst].size(); ++i){
		unsigned v = con[dst][i];
		if (v2p[v] == -1) continue;

		v2space[v2p[v]][1] = 1; // 婊¤冻鏉′欢鐨刣st鐨勯偦灞呯偣閮芥湁浜嗕竴鏉¤矾寰
	}

	for (int hop=2; hop<khop+1; ++hop){

		for (int i=0; i<numV; ++i){

			if (v2p[i] == -1) continue;

			for (int j=0; j<con[i].size(); ++j){ // 閬嶅巻i鐐圭殑婊¤冻鏉′欢鐨勯偦灞呯偣
				int vv = con[i][j];
				if (v2p[vv] == -1 or vv == src or vv == dst)
					continue;

				v2space[v2p[i]][hop] += (v2space[v2p[vv]][hop-1]);
//				if (v2space[v2p[vv]][hop-1] > 0)
//					v2space[v2p[i]][hop] -= v2space[v2p[i]][hop-2];
			}
		}
	}

	cout<<v2space[v2p[src]][khop]<<endl;
}


void Search_Space_Join(int src, int dst, int numV, int khop){
    unsigned q1 = khop/2, q2 = khop%2;
    Lmax = q1+q2, Rmax = q1; // 宸 =鍙  or 宸 =鍙 +1
	// 鍏辨湁active_nums涓紝姣忎釜鍏冪礌閮藉瓨鍌 0-khop鐨勮矾寰勬暟

	v2space.resize(active_nums, vector<long long>(Lmax+1));
	v2space[v2p[dst]][0] = 1; // 鍙湁dst鑷韩

	v2space_Reverse.resize(active_nums, vector<long long>(Lmax+1));
	v2space_Reverse[v2p[src]][0] = 1; // 鍙湁dst鑷韩

	for (int i=0; i<(int)con[dst].size(); ++i){
		unsigned v = con[dst][i];

		if (v2p[v] == -1)
			continue;

		v2space[v2p[v]][1] = 1; //
	}

	for (int i=0; i<(int)con[src].size(); ++i){
		unsigned v = con[src][i];

		if (v2p[v] == -1)
			continue;

		v2space_Reverse[v2p[v]][1] = 1; // 婊¤冻鏉′欢鐨刣st鐨勯偦灞呯偣閮芥湁浜嗕竴鏉¤矾寰
	}

	// Lmax >= Rmax 鎭掓垚绔
	for (int hop=2; hop<Lmax+1; ++hop){
		for (int i=0; i<numV; ++i){
			if (v2p[i] == -1) continue;

			for (int j=0; j<con[i].size(); ++j){ // 閬嶅巻i鐐圭殑婊¤冻鏉′欢鐨勯偦灞呯偣
				int vv = con[i][j];
				if (v2p[vv] == -1 or vv == src or vv == dst)
					continue;

				v2space[v2p[i]][hop] += (v2space[v2p[vv]][hop-1]);
			}

			for (int j=0; j<con_R[i].size(); ++j){ // 閬嶅巻i鐐圭殑婊¤冻鏉′欢鐨勯偦灞呯偣
				int vv = con_R[i][j];
				if (v2p[vv] == -1 or vv == src or vv == dst)
					continue;

				v2space_Reverse[v2p[i]][hop] += (v2space_Reverse[v2p[vv]][hop-1]);
			}
		}
	}
}



void PathSelect(unsigned u, unsigned dst, unsigned khop, long long theta, int ff){
	s.push_back(u);
	flag[u] = 1;

	for (int i=0; i<(int)con[u].size(); ++i){
		int v = con[u][i];

		if ( v2p[v] == -1 || flag[v] == 1 ) continue;

		if ( s.size() + distance_[v].second > khop ) break;

		if (v == dst){
			if (ff == 0)
				totalPath += 1;
			else{
				if (MFlag_Right[v2p[s[0]]][s.size()] == 1){
//					cout<<" **** "<<endl;
					s.push_back(v);
					Paths.push_back(s); // 杩涗竴姝ユ帰绱㈠嚭 dst 灏卞彲浠
					s.pop_back(); // 閲嶆柊杩斿洖鍒  v 鐐
				}
			}
			continue;
		}

		int offset = khop - s.size() + 1; // 瀛樺湪1鐨勫樊鍊
		long long paths = 0;

		for (int kk=1; kk<offset+1; kk++)
			paths += v2space[v2p[v]][kk];

		if (paths <= theta){
//			cout<<"  --11--  "<<endl;
			s.push_back(v);
			Paths.push_back(s); // 褰撳墠璺緞鍙互鐩存帴鏋氫妇锛屼唬浠峰彲鎵垮彈
			s.pop_back(); // 閲嶆柊杩斿洖鍒  v 鐐
		}else
			PathSelect(v, dst, khop, theta, ff);
	}

	s.pop_back();
	flag[u] = 0;
	return;
}


void PathSelect_parallel(unsigned u, unsigned dst, unsigned khop, long long theta,
						 int ff, int pid){
	s_thread[pid].push_back(u);
	flag_thread[pid][u] = 1;

	for (int i=0; i<(int)con[u].size(); ++i){
		int v = con[u][i];

		if ( v2p[v] == -1 || flag_thread[pid][v] == 1 ) continue;

		if ( s_thread[pid].size() + distance_[v].second > khop ) break;

		if (v == dst){
			if (ff == 0){
//				totalPath += 1;
				continue;
			}else{
				if (MFlag_Right[v2p[s_thread[pid][0]]][s_thread[pid].size()] == 1){
					s_thread[pid].push_back(v);
					Pth_thread[pid].push_back(s_thread[pid]); // 杩涗竴姝ユ帰绱㈠嚭 dst 灏卞彲浠
					s_thread[pid].pop_back(); // 閲嶆柊杩斿洖鍒  v 鐐
				}
			}
			continue;
		}

		int offset = khop - s_thread[pid].size() + 1; // 瀛樺湪1鐨勫樊鍊
		long long paths = 0;

		for (int kk=1; kk<offset+1; kk++)
			paths += v2space[v2p[v]][kk];

		if (paths <= theta){
			s_thread[pid].push_back(v);
			Pth_thread[pid].push_back(s_thread[pid]); // 褰撳墠璺緞鍙互鐩存帴鏋氫妇锛屼唬浠峰彲鎵垮彈
			s_thread[pid].pop_back(); // 閲嶆柊杩斿洖鍒  v 鐐
		}else
			PathSelect_parallel(v, dst, khop, theta, ff, pid);
	}

	s_thread[pid].pop_back();
	flag_thread[pid][u] = 0;
	return;
}




void PathSelect_Reverse_parallel(unsigned u, unsigned src, unsigned khop, long long theta, int ff,
						int pid){
	// 浠庝腑闂寸偣鍘诲埌src鐐  浣跨敤 v2space_Reverse, con_R
	s_thread[pid].push_back(u);
	flag_thread[pid][u] = 1;

	for (int i=0; i<(int)con_R[u].size(); ++i){
		int v = con_R[u][i];

		if ( v2p[v] == -1 || flag_thread[pid][v] == 1 ) continue;

		if ( s_thread[pid].size() + distance_[v].first > khop ) break;

		if (v == src){
			if (ff == 0){
				continue;
//				totalPath += 1;
			}else{
				if (MFlag_Left[v2p[s_thread[pid][0]]][s_thread[pid].size()] == 1){
					s_thread[pid].push_back(v);
					Pth_R_thread[pid].push_back(s_thread[pid]);
					s_thread[pid].pop_back(); // 閲嶆柊杩斿洖鍒  v 鐐
				}
			}
			continue;
		}

		int offset = khop - s_thread[pid].size() + 1; // 瀛樺湪1鐨勫樊鍊
		long long paths = 0;
		for (int kk=1; kk<offset+1; kk++)
			paths += v2space_Reverse[v2p[v]][kk];

		if (paths <= theta){
			s_thread[pid].push_back(v);
			Pth_R_thread[pid].push_back(s_thread[pid]); // 褰撳墠璺緞鍙互鐩存帴鏋氫妇锛屼唬浠峰彲鎵垮彈
			s_thread[pid].pop_back(); // 閲嶆柊杩斿洖鍒  v 鐐
		}else
			PathSelect_Reverse_parallel(v, src, khop, theta, ff, pid);
	}

	s_thread[pid].pop_back();
	flag_thread[pid][u] = 0;
	return;
}


void PathSelect_Reverse(unsigned u, unsigned src, unsigned khop, long long theta, int ff){
	// 浠庝腑闂寸偣鍘诲埌src鐐  浣跨敤 v2space_Reverse, con_R
	s.push_back(u);
	flag[u] = 1;

	for (int i=0; i<(int)con_R[u].size(); ++i){
		int v = con_R[u][i];

		if ( v2p[v] == -1 || flag[v] == 1 ) continue;

		if ( s.size() + distance_[v].first > khop ) break;

		if (v == src){
			if (ff == 0)
				totalPath += 1;
			else{
				if (MFlag_Left[v2p[s[0]]][s.size()] == 1){
//					cout<<" ### "<<endl;
					s.push_back(v);
					Paths_Reverse.push_back(s);
					s.pop_back(); // 閲嶆柊杩斿洖鍒  v 鐐
				}
			}
			continue;
		}

		int offset = khop - s.size() + 1; // 瀛樺湪1鐨勫樊鍊
		long long paths = 0;
		for (int kk=1; kk<offset+1; kk++)
			paths += v2space_Reverse[v2p[v]][kk];

		if (paths <= theta){
//			cout<<"  --22--  "<<endl;
			s.push_back(v);
			Paths_Reverse.push_back(s); // 褰撳墠璺緞鍙互鐩存帴鏋氫妇锛屼唬浠峰彲鎵垮彈
			s.pop_back(); // 閲嶆柊杩斿洖鍒  v 鐐
		}else
			PathSelect_Reverse(v, src, khop, theta, ff);
	}

	s.pop_back();
	flag[u] = 0;
	return;
}









void DFS_Multi_Single(unsigned u, unsigned dst, unsigned khop){
	// 鐩存帴閬嶅巻u鐨勯偦灞呯偣锛
	s.push_back(u);
	flag[u] = 1;

	for (int i=0; i<(int)con[u].size(); ++i){
		unsigned v = con[u][i];

		if (s.size() + distance_[v].second > khop ) break;

		if (v == dst){

			totalPath += 1;
		}else if (flag[v] == 0){
			DFS_Multi_Single(v, dst, khop);
		}else{

		}
	}

	s.pop_back();
	flag[u] = 0;

	return;
}


void DFS_Multi(unsigned u, unsigned dst, unsigned khop,
		vector<unsigned>& flag_, vector<unsigned>& s_,
		long long& localPath){
	// 鐩存帴閬嶅巻u鐨勯偦灞呯偣锛  tr1::unordered_map<unsigned, int>&
	s_.push_back(u);
	flag_[v2p[u]] = 1;

	for (int i=0; i<(int)con[u].size(); ++i){
		unsigned v = con[u][i];

		if (s_.size() + distance_[v].second > khop ) break;

		if (v == dst){
			localPath += 1;
//			Cnts[pid][s_.size()-1] += 1;
//			for (int kkk=0; kkk<s_.size(); ++kkk)
//				cout<<s_[kkk]<<"  ";
//			cout<<dst<<endl;
		}else if (flag_[v2p[v]] == 0){
			DFS_Multi(v, dst, khop, flag_, s_, localPath);
		}else{

		}
	}

	s_.pop_back();
	flag_[v2p[u]] = 0;

	return;
}


void DFSJoinLpath(unsigned u, unsigned dst, unsigned khop,
		vector<unsigned>& flag_, vector<unsigned>& s_,
		vector<vector<unsigned> >& Lpaths, int& Lp){
	// 璇ョ▼搴忓皢鏂扮殑璺緞鎷兼帴鎴  vector褰㈠紡, Lp鏄搴旂殑浣嶇疆
	s_.push_back(u);
	flag_[v2p[u]] = 1;
	int place = s_.size();

	for (int i=0; i<(int)con_R[u].size(); ++i){
		unsigned v = con_R[u][i];

		if (place + distance_[v].first > khop ) break;

//		cout<<" "<<u<<" - "<<v<<endl;

		if (v == dst){
			unsigned pla = v2p[s_[1]];
			int f_ = MFlag_Left[pla][place-1];

			if (f_ == 1){ // lens: hop璺虫暟   sss[lens]: 瀵瑰簲lens鐨勪綅缃  and s_.size()>2
				#pragma omp critical
				{
//					cout<<Lp<<"  "<<s_.size()<<endl;
					Lpaths[Lp] = s_;
					Lp += 1;
				}
			}
		}else if (flag_[v2p[v]] == 0){
			DFSJoinLpath(v, dst, khop, flag_, s_, Lpaths, Lp);
		}else{

		}
	}

	s_.pop_back();
	flag_[v2p[u]] = 0;

	return;

}

void DFSJoinRpath(unsigned u, unsigned dst, unsigned khop,
		vector<unsigned>& flag_, vector<unsigned>& s_,
		unordered_map<int, vector<vector<vector<unsigned> > > >& Rpaths){
	// 璇ョ▼搴忓皢鏂扮殑璺緞鎷兼帴鎴  vector褰㈠紡, Lp鏄搴旂殑浣嶇疆
	s_.push_back(u);
	flag_[v2p[u]] = 1;
	int place = s_.size();

	for (int i=0; i<(int)con[u].size(); ++i){
		unsigned v = con[u][i];

		if (place + distance_[v].second > khop ) break;

		if (v == dst){
			unsigned pla = v2p[s_[1]];
			int f_ = MFlag_Right[pla][place-1];

			if (f_ == 1){ // lens: hop璺虫暟   sss[lens]: 瀵瑰簲lens鐨勪綅缃
				int vnode = s_[1], lens = s_.size()-1;

				#pragma omp critical
				{
//					cout<<" Right:  "<<s_.size()<<endl;
					Rpaths[vnode][lens].push_back(s_); // 添加到map中对应的位置
				}
			}
		}else if (flag_[v2p[v]] == 0){
			DFSJoinRpath(v, dst, khop, flag_, s_, Rpaths);
		}else{

		}
	}

	s_.pop_back();
	flag_[v2p[u]] = 0;

	return;

}


void DFS_Join(unsigned u, unsigned dst, unsigned khop,
		vector<unsigned>& flag_, vector<unsigned>& s_, int ff,
		vector<vector<pth> >& paths,
		vector<long long>& sss){
	// 鐩存帴閬嶅巻u鐨勯偦灞呯偣锛  tr1::unordered_map<unsigned, int>&
	s_.push_back(u);
	flag_[v2p[u]] = 1;
	int place = s_.size();

	if (ff == 0){ // 鍙嶅悜浼犳挱
		for (int i=0; i<(int)con_R[u].size(); ++i){
			unsigned v = con_R[u][i];

			if (place + distance_[v].first > khop ) break;

			if (v == dst){
				unsigned pla = v2p[s_[0]];
				int f_ = MFlag_Left[pla][place];

				if (f_ == 1){ // lens: hop璺虫暟   sss[lens]: 瀵瑰簲lens鐨勪綅缃
					paths[place][sss[place]]=s_; //make_pair(lens, );
					sss[place] += 1;
				}

			}else if (flag_[v2p[v]] == 0){
				DFS_Join(v, dst, khop, flag_, s_, ff, paths, sss);
			}else{

			}
		}

	}else{
		for (int i=0; i<(int)con[u].size(); ++i){
			unsigned v = con[u][i];

			if (place + distance_[v].second > khop ) break;

			if (v == dst){

				unsigned pla = v2p[s_[0]];
				int f_ = MFlag_Right[pla][place];

				if (f_ == 1){
					paths[place][sss[place]]=pth(s_); //make_pair(lens, );
					sss[place] += 1;
				}

			}else if (flag_[v2p[v]] == 0){
				DFS_Join(v, dst, khop, flag_, s_, ff, paths, sss);
			}else{

			}
		}

	}

	s_.pop_back();
	flag_[v2p[u]] = 0;

	return;
}


void DFS_Join(unsigned u, unsigned dst, unsigned khop,
		vector<unsigned>& flag_, pth& s_, int ff,
		vector<vector<pth> >& paths,
		vector<long long>& sss, long long& total, int& Now,
		int& Bound){
	// 鐩存帴閬嶅巻u鐨勯偦灞呯偣锛  tr1::unordered_map<unsigned, int>&
	s_.p.push_back(u);
	flag_[v2p[u]] = 1;
	int place = s_.p.size();

	if (ff == 0){ // 鍙嶅悜浼犳挱
		for (int i=0; i<(int)con_R[u].size(); ++i){
			unsigned v = con_R[u][i];

			if (place + distance_[v].first > khop ) break;

			if (v == dst){
				unsigned pla = v2p[s_.p[0]];
				int f_ = MFlag_Left[pla][place];

				if (f_ == 1){ // lens: hop璺虫暟   sss[lens]: 瀵瑰簲lens鐨勪綅缃
					total += 1; // 绗﹀悎瑕佹眰鐨勮矾寰勬暟閲 +1
					if (total % Bound == Now){
						paths[place][sss[place]]=s_; //make_pair(lens, );
						sss[place] += 1;
					}
				}

			}else if (flag_[v2p[v]] == 0){
				DFS_Join(v, dst, khop, flag_, s_, ff, paths,
						 sss, total, Now, Bound);
			}else{

			}
		}

	}else{
		for (int i=0; i<(int)con[u].size(); ++i){
			unsigned v = con[u][i];

			if (place + distance_[v].second > khop ) break;

			if (v == dst){

				unsigned pla = v2p[s_.p[0]];
				int f_ = MFlag_Right[pla][place];

				if (f_ == 1){
					total += 1; // 绗﹀悎瑕佹眰鐨勮矾寰勬暟閲 +1
					if (total % Bound == Now){
						paths[place][sss[place]]=s_; //make_pair(lens, );
						sss[place] += 1;
					}
				}

			}else if (flag_[v2p[v]] == 0){
				DFS_Join(v, dst, khop, flag_, s_, ff, paths,
						 sss, total, Now, Bound);
			}else{

			}
		}

	}

	s_.p.pop_back();
	flag_[v2p[u]] = 0;

	return;
}


void PathJoin(vector<vector<pth> >& LP, vector<vector<pth> >& RP,
			  vector<unsigned>& elems,  vector<long long>& s1,
			  vector<long long>& s2,    long long& nums){

		// == 鍏堥亶鍘  0-Lmax ==
	for (int i=0; i<=Lmax; ++i){

		if (s1[i] == 0) continue;

		for (int ii=0; ii<s1[i]; ++ii){
			pth& L1 = LP[i][ii];

			for(int k=1; k<L1.p.size(); ++k)
				elems[v2p[L1.p[k]]] = 1;

			// == 鐒跺悗瑕佸畾浣嶅埌    RP 涓殑鐩稿叧鍏冪礌
			int start = i-1>=0? i-1:0, end = i<=Rmax? i:Rmax;
			for (int j=start; j<=end; ++j){

				if (s2[j] == 0) continue;

				for (int jj=0; jj<s2[j]; ++jj){

					pth& R1 = RP[j][jj];

					int ff = 1;
					for (int jk=1; jk<R1.p.size(); ++jk){
						if(elems[v2p[R1.p[jk]]] == 1){
							ff = 0; // 瀛樺湪閲嶅鍏冪礌
							break;
						}
					}

					if (ff == 1){
						nums += 1;
//						cout<<src<<"  ";
//						for(int k=L1.p.size()-1; k>=0; --k)
//							cout<<L1.p[k]<<"  ";
//						for(int k=1; k<R1.p.size(); ++k)
//							cout<<R1.p[k]<<"  ";
//						cout<<dst<<endl;
					}
				}
			}

			for(int k=1; k<L1.p.size(); ++k)
				elems[v2p[L1.p[k]]] = 0;
		}
	}
}


void PathJoin_R(vector<vector<pth> >& LP, vector<vector<pth> >& RP,
			  vector<unsigned>& elems,  vector<long long>& s1,
			  vector<long long>& s2,    long long& nums){

		// == 鍏堥亶鍘  0-Lmax ==
	for (int i=0; i<=Rmax; ++i){

		if (s2[i] == 0) continue;

		for (int ii=0; ii<s2[i]; ++ii){
			pth& R1 = RP[i][ii];

			for(int k=1; k<R1.p.size(); ++k)
				elems[v2p[R1.p[k]]] = 1;

			// == 鐒跺悗瑕佸畾浣嶅埌    RP 涓殑鐩稿叧鍏冪礌
			int start = i, end = i+1<=Lmax? i+1:Lmax;
			for (int j=start; j<=end; ++j){

				if (s1[j] == 0) continue;

				for (int jj=0; jj<s1[j]; ++jj){

					pth& L1 = LP[j][jj];

					int ff = 1;
					for (int jk=1; jk<L1.p.size(); ++jk){
						if(elems[v2p[L1.p[jk]]] == 1){
							ff = 0; // 瀛樺湪閲嶅鍏冪礌
							break;
						}
					}

					if (ff == 1){
						nums += 1;
//						cout<<src<<"  ";
//						for(int k=L1.p.size()-1; k>=0; --k)
//							cout<<L1.p[k]<<"  ";
//						for(int k=1; k<R1.p.size(); ++k)
//							cout<<R1.p[k]<<"  ";
//						cout<<dst<<endl;
					}
				}
			}

			for(int k=1; k<R1.p.size(); ++k)
				elems[v2p[R1.p[k]]] = 0;
		}
	}
}


void Zeng_Baseline(int src, int dst, int numV, int khop){
	// 鏋勫缓杞婚噺绾х储寮曪紝纭畾鍙傛暟
	cout<<"Zeng baseline:"<<endl;
	t111 = omp_get_wtime();
	BuildIndex2(src, dst, numV, khop); // 鎺掗櫎鍐椾綑鐐  (鍩烘湰鏃犳敼杩 )
	cout<<"  pre:  "<<omp_get_wtime()-t111<<"  s"<<endl;
 	Search_Space(src, dst, numV, khop); // 纭畾椤剁偣鐨勮矾寰勪笂闄愬   (鍩烘湰鏃犳敼杩 )

	long long TPaths = accumulate(v2space[v2p[src]].begin(),
			v2space[v2p[src]].end(), 0.0);
	long long theta1 = 2000000000000; // long(TPaths / (k*threads))

	PathSelect(src, dst, khop, theta1, 0);

	long long totalSize = Paths.size(), nums=0, maxOne=0;
	double maxTime = 0, averageTime = 0;
	unsigned maxVid, maxK;

	vector<vector<unsigned> > Flag_(threads, vector<unsigned>(active_nums));
//	Cnts.resize(threads, vector<unsigned>(khop+1));


	cout<<"Size: "<<totalSize<<" theta1: "<<theta1<<endl;


	omp_set_num_threads(threads);

	#pragma omp parallel
	{
		int pid = omp_get_thread_num(), np = omp_get_num_threads();
		double t1 = omp_get_wtime();

		for (int u=pid; u<totalSize; u+=np){
			// flag涓嶈兘鐢╲ector
			double t = omp_get_wtime();

			vector<unsigned>& flag_ = Flag_[pid];
			long long numP = 0, kk = 0;
			int vv = Paths[u][Paths[u].size()-1];
			Paths[u].pop_back();

			for(int ij=0; ij<Paths[u].size(); ++ij){
				unsigned vv = Paths[u][ij];
				flag_[v2p[vv]] = 1;
			}

			DFS_Multi(vv, dst, khop, flag_, Paths[u], numP);

			for(int ij=0; ij<Paths[u].size(); ++ij){
				unsigned vv = Paths[u][ij];
				flag_[v2p[vv]] = 0;
			}

			vector<unsigned>().swap(Paths[u]);

			if (maxTime < omp_get_wtime()-t)
				maxTime = omp_get_wtime()-t;

			averageTime += omp_get_wtime()-t;

			#pragma omp critical
			{
				totalPath += numP;
				nums += 1;
			}

//			if (totalPath > MaxPaths and global_fff == 0){
//				global_fff += 1;
//				cout<<totalPath<<"   time: "<<omp_get_wtime()-t111<<endl;
//			}

			if (nums > 10 and nums % 5000000 == 0)
				cout<<"Deal numbers: "<<nums<<" time: "<<omp_get_wtime()-t1<<endl;
		}
	}

	cout<<"Parallel: "<<totalPath<<"  Predicted:"<<TPaths<<endl;

//	cout<<"Max time: "<<maxTime<<"  Average Time: "<<averageTime/float(totalSize)<<endl;
//	cout<<"Max Paths: "<<maxOne<<"  Predicted Paths: "<<theta<<endl;

}


void Join_initial(){
	Lpaths.resize(threads, vector<vector<pth> >(Lmax+1) );
	Rpaths.resize(threads, vector<vector<pth> >(Lmax+1) );

	omp_set_num_threads(threads);
	#pragma omp parallel
	{
		int pid = omp_get_thread_num(), np = omp_get_num_threads();
		for (int u=pid; u<threads; u+=np){
			for (int i=0; i<Lmax+1; i++){
				Lpaths[pid][i].resize(maxL[i]+2);
				Rpaths[pid][i].resize(maxR[i]+2);
			}
		}
	}
}


pair<int, long long> num(long long val, vector<long long>& vec){

	long long sum0=0, sum1=vec[0];

	for (int i=0; i<vec.size()-1; ++i){


		if (val >= sum0 and val < sum1)
			return make_pair(i, (long long)(val-sum0));

		sum0 += vec[i], sum1 += vec[i+1];
	}

	return make_pair(vec.size()-1, (long long)(val-sum0));
}


void VertexDivide(vector<vector<unsigned> >& vM,
		          vector<pair<long long, int> >& vPath,
		          vector<long long>& paths){

	for (int i=0; i<vPath.size(); ++i){
		int minP = min_element(paths.begin(),paths.end()) - paths.begin();

		vM[minP].push_back(vPath[i].second);
		paths[minP] += vPath[i].first;
	}

//	for (int i=0; i<vM.size(); ++i)
//		cout<<i<<"  "<<vM[i].size()<<"  "<<paths[i]<<endl;
}


void PathSelectJoin(unsigned u, unsigned dst, unsigned khop, long long theta, int ff,
		vector<vector<unsigned> >& Pth){
	s.push_back(u);
	flag[u] = 1;

	if (ff == 0){
		for (int i=0; i<(int)con[u].size(); ++i){
			int v = con[u][i];

			if ( v2p[v] == -1 || flag[v] == 1 ) continue;

			if ( s.size() + distance_[v].second > khop ) break;

			if (v == dst){
				int fff = MFlag_Right[v2p[s[1]]][s.size()-1];//:MFlag_Left[v2p[s[0]]][s.size()];
				if (fff == 1){ // 2hop鐨勫凡缁忕粺璁″畬浜
					s.push_back(v);
					Pth.push_back(s); // 杩涗竴姝ユ帰绱㈠嚭 dst 灏卞彲浠
					s.pop_back(); // 閲嶆柊杩斿洖鍒  v 鐐
				}
				continue;
			}

			int offset = khop - s.size() + 1; // 瀛樺湪1鐨勫樊鍊
			long long paths = 0, vals;

			for (int kk=1; kk<offset+1; kk++){
				vals = v2space[v2p[v]][kk];//:v2space_Reverse[v2p[v]][kk];
				paths += vals;
			}

			if (paths <= theta){
				s.push_back(v);
				Pth.push_back(s); // 褰撳墠璺緞鍙互鐩存帴鏋氫妇锛屼唬浠峰彲鎵垮彈
				s.pop_back(); // 閲嶆柊杩斿洖鍒  v 鐐
			}else
				PathSelectJoin(v, dst, khop, theta, ff, Pth);
		}
	}else{
		for (int i=0; i<(int)con_R[u].size(); ++i){
			int v = con_R[u][i];

			if ( v2p[v] == -1 || flag[v] == 1 ) continue;

			if ( s.size() + distance_[v].first > khop ) break;

			if (v == dst){
				int fff = MFlag_Left[v2p[s[1]]][s.size()-1];//:MFlag_Left[v2p[s[0]]][s.size()];
				if (fff == 1){ // 2hop鐨勫凡缁忕粺璁″畬浜
					s.push_back(v);
					Pth.push_back(s); // 杩涗竴姝ユ帰绱㈠嚭 dst 灏卞彲浠
					s.pop_back(); // 閲嶆柊杩斿洖鍒  v 鐐
				}
				continue;
			}

			int offset = khop - s.size() + 1; // 瀛樺湪1鐨勫樊鍊
			long long paths = 0, vals;

			for (int kk=1; kk<offset+1; kk++){
				vals = v2space_Reverse[v2p[v]][kk];//:v2space_Reverse[v2p[v]][kk];
				paths += vals;
			}

			if (paths <= theta){
				s.push_back(v);
				Pth.push_back(s); // 褰撳墠璺緞鍙互鐩存帴鏋氫妇锛屼唬浠峰彲鎵垮彈
				s.pop_back(); // 閲嶆柊杩斿洖鍒  v 鐐
			}else
				PathSelectJoin(v, dst, khop, theta, ff, Pth);
		}
	}

	s.pop_back();
	flag[u] = 0;
	return;
}


void MiddlePart(unsigned src, unsigned dst, int numV, int khop){

	unsigned Lhop=1, Rhop=1;

    long long theta = 500000000000, nums = 0, th1 = theta;

    initial_parameters(src, dst, Lmax, Rmax);

    vector<unsigned> a_L, a_R;

	while (1){
		// .first=Lhop鐨勭偣鍏堟洿鏂
		vector<unsigned> L_(active_nums, -1000), R_(active_nums, -1000);

		for (int i=0; i<numV; i++){
			if (v2p[i] == -1)
				continue;

			int left = disL_[v2p[i]];

			if (left == Lhop){ // 琛ㄧず鍦ㄨ鎯呭喌涓嬶紝椤剁偣灞炰簬 left+right hop 鐨勪腑闂磋矾寰
				for (int ii=0; ii<con[i].size(); ++ii){
					unsigned v_ = con[i][ii];

					if (v2p[v_] == -1) continue;

					if (v_ == src || v_ == dst) continue;

					L_[v2p[v_]] = Lhop+1;

					if (L_[v2p[v_]] == disR_[v2p[v_ ]]+1){

						if (MFlag_Left[v2p[v_]][L_[v2p[v_]]] == 0){ // 璁板綍涓 涓嬪湪Lhop澶勭殑棰勬祴璺緞鏁伴噺
							MFlag_Left[v2p[v_]][L_[v2p[v_]]] = 1;
							path_src[v2p[v_]] += 1; // L_[v2p[v_]]
						}

						if (MFlag_Right[v2p[v_]][disR_[v2p[v_ ]]] == 0){
							MFlag_Right[v2p[v_]][disR_[v2p[v_ ]]] = 1;
							path_dst[v2p[v_]] += 1; // disR_[v2p[v_]]
						}
					}
				}
			}
		}

		disL_.swap(L_); // 鍏ㄩ儴鏇挎崲
		Lhop += 1;

		if (Lhop + Rhop == khop) {
			vector<unsigned>().swap(disL_);
			vector<unsigned>().swap(disR_);
			break;
		}

		for (int i=0; i<numV; i++){
			if (v2p[i] == -1) continue;

			int right = disR_[v2p[i]];

			if (right == Rhop){ // 琛ㄧず鍦ㄨ鎯呭喌涓嬶紝椤剁偣灞炰簬 left+right hop 鐨勪腑闂磋矾寰
				for (int ii=0; ii<con[i].size(); ++ii){
					unsigned v_ = con[i][ii];
					if (v2p[v_] == -1)
						continue;

					if (v_ == src || v_ == dst) continue;

					R_[v2p[v_]] = Rhop+1;
					if (disL_[v2p[v_ ]] == R_[v2p[v_]]){

						if (MFlag_Left[v2p[v_]][disL_[v2p[v_ ]]] == 0){ // 璁板綍涓 涓嬪湪Lhop澶勭殑棰勬祴璺緞鏁伴噺
							MFlag_Left[v2p[v_]][disL_[v2p[v_ ]]] = 1;
							path_src[v2p[v_]] += 1; // disL_[v2p[v_ ]]
						}

						if (MFlag_Right[v2p[v_]][R_[v2p[v_]]] == 0){
							MFlag_Right[v2p[v_]][R_[v2p[v_]]] = 1;
							path_dst[v2p[v_]] += 1; // R_[v2p[v_]]
						}
					}
				}
			}
		}

		disR_.swap(R_); // 鍏ㄩ儴鏇挎崲
		Rhop += 1;
		if (Lhop + Rhop == khop) {
			vector<unsigned>().swap(disL_);
			vector<unsigned>().swap(disR_);
			break;
		}
	}

	// v2Middle收集待处理的元素, v2Decompose收集待分解的元素

	for (int i=0; i<numV; ++i){
		if (v2p[i] == -1 or (path_src[v2p[i]] == 0 and path_dst[v2p[i]] == 0)){ //
			continue;
		}

		if (i == src or i==dst) continue;

		v2Decompose.push_back(midd2(i, i));
	}

	Elems.resize(threads, vector<unsigned>(active_nums));
	Flag_.resize(threads, vector<unsigned>(active_nums));
	vector<vector<midd2> > v2M, v2Dmp;
	vector<unsigned> elem_(active_nums);

	cout<<v2Decompose.size()<<endl;

	while(1){

		v2M.resize(threads), v2Dmp.resize(threads);
		if (v2Decompose.size() == 0)
			break;

		#pragma omp parallel for num_threads(threads)
		for (int i=0; i<v2Decompose.size(); i++){
//			cout<<"i: "<<i<<endl;
			int pid = omp_get_thread_num();

			midd2& mid = v2Decompose[i];
			vector<vector<unsigned> > LP, RP;

			// == 处理 mid.lp 以及 rp ==
			int hop1 = mid.rp.size()-1, v1 = mid.rp[hop1], offset1 = Rmax-hop1;
			long long Rpaths = 0, Lpaths = 0;

			if (v1 == dst)
				Rpaths = 0;
			else
				for (int kk=1; kk<offset1+1; kk++)
					Rpaths += v2space[v2p[v1]][kk];

			if ( Rpaths > theta){ // 基于con进行遍历
				int ff1 = 0;
				for (int i=0; i<mid.rp.size(); ++i)
					Flag_[pid][v2p[mid.rp[i]]] = 1;
				Flag_[pid][v2p[src]] = 1;


				for (int i=0; i<con[v1].size(); ++i){
					int u = con[v1][i];

					if (v2p[u] == -1 or Flag_[pid][v2p[u]] == 1) continue;

					if (hop1+1+distance_[u].second > Rmax) break;

					if (u == dst){
						if (MFlag_Right[v2p[mid.rp[0]]][mid.rp.size()] == 1){
							mid.rp.push_back(u);
							RP.push_back(mid.rp);
							mid.rp.pop_back();
						}
					}else{
						ff1 += 1;
						mid.rp.push_back(u);
						RP.push_back(mid.rp);
						mid.rp.pop_back();
					}
				}

				for (int i=0; i<mid.rp.size(); ++i)
					Flag_[pid][v2p[mid.rp[i]]] = 0;
				Flag_[pid][v2p[src]] = 0;

				if (ff1 == 0)
					RP.push_back(mid.rp);
			}else{
				RP.push_back(mid.rp);
			}


			Flag_[pid].clear();
			int hop2 = mid.lp.size()-1, v2 = mid.lp[hop2], offset2 = Lmax-hop2;

			if (v2 == src)
				Lpaths = 0;
			else
				for (int kk=1; kk<offset2+1; kk++)
					Lpaths += v2space_Reverse[v2p[v2]][kk];

			if ( Lpaths > theta ){ // 基于con进行遍历
				int ff1 = 0;
				for (int i=0; i<mid.lp.size(); ++i)
					Flag_[pid][v2p[mid.lp[i]]] = 1;
				Flag_[pid][v2p[dst]] = 1;


				for (int i=0; i<con_R[v2].size(); ++i){
					int u = con_R[v2][i];

					if (v2p[u] == -1 or Flag_[pid][v2p[u]] == 1) continue;

					if (hop2+1+distance_[u].first > Lmax) break;

					if (u == src){
						if (MFlag_Left[v2p[mid.lp[0]]][mid.lp.size()] == 1){
							mid.lp.push_back(u);
							LP.push_back(mid.lp);
							mid.lp.pop_back();
						}
					}else{
						ff1 += 1;
						mid.lp.push_back(u);
						LP.push_back(mid.lp);
						mid.lp.pop_back();
					}


				}

				for (int i=0; i<mid.lp.size(); ++i)
					Flag_[pid][v2p[mid.lp[i]]] = 0;
				Flag_[pid][v2p[dst]] = 0;


				if (ff1 = 0){
					LP.push_back(mid.lp);
				}
			}else{
				LP.push_back(mid.lp);
			}

//			if (iij > 1)
//				cout<<LP.size()<<"  "<<RP.size()<<endl;

			// == 组合成执行任务 ==
			int hps1 = 0, hps2 = 0;
			long long lpth = 0, rpth = 0;

			for (int i=0; i<LP.size(); ++i){
				vector<unsigned>& llp = LP[i];
				hps1 = llp.size()-1;
				int vL = llp[hps1];

				if (vL == src)
					lpth = 0;
				else
					for (int kk=1; kk<Lmax-hps1+1; kk++)
						lpth += v2space_Reverse[v2p[vL]][kk];

				// ====  统计元素    ====
				for (int kj=1; kj<llp.size(); ++kj){
					elem_[v2p[ llp[kj] ]] = 1;
				}

				for (int j=0; j<RP.size(); ++j){
					vector<unsigned>& rrp = RP[j];
					hps2 = rrp.size()-1;
					int vR = rrp[hps2], ff2 = 0;
					for (int kj=1; kj<rrp.size(); ++kj){
						if (elem_[v2p[ rrp[kj] ]] == 1){
							ff2 = 1; break;
						}
					}

					if (ff2 == 0){
						if (vR == dst)
							rpth = 0;
						else
							for (int kk=1; kk<Rmax-hps2+1; kk++)
								rpth += v2space[v2p[vR]][kk];

						if (lpth <= theta and rpth <= theta){
							v2M[pid].push_back(midd2(llp, rrp));
						}else{
							v2Dmp[pid].push_back(midd2(llp, rrp));
						}
						rpth = 0;
					}
				}

				for (int kj=1; kj<llp.size(); ++kj){
					elem_[v2p[ llp[kj] ]] = 0;
				}
				lpth = 0;
			}

			vector<vector<unsigned> >().swap(LP);
			vector<vector<unsigned> >().swap(RP);
		}



		vector<midd2>().swap(v2Decompose);
		for (int x=0; x<threads; ++x){
			v2Middle.insert(v2Middle.end(), v2M[x].begin(), v2M[x].end());
			vector<midd2>().swap(v2M[x]);
			v2Decompose.insert(v2Decompose.end(), v2Dmp[x].begin(), v2Dmp[x].end());
			vector<midd2>().swap(v2Dmp[x]);
		}

		vector<vector<midd2> >().swap(v2M);
		vector<vector<midd2> >().swap(v2Dmp);

//		if (v2Middle.size() == 0 and v2Decompose.size()>0)
		theta *= 2;


		cout<<"size: "<<v2Middle.size()<<"  "<<v2Decompose.size()<<"  "<<theta<<endl;
	}

//	for (int i=0; i<v2Middle.size(); ++i){
//		vector<unsigned> & v1 = v2Middle[i].lp, &v2 = v2Middle[i].rp;
//
//		for (int ii=0; ii<v1.size(); ++ii)
//			cout<<v1[v1.size()-ii-1]<<" ";
////		cout<<endl;
//
//		for (int ii=1; ii<v2.size(); ++ii)
//			cout<<v2[ii]<<" ";
//		cout<<endl;
//		cout<<endl;
//	}


	maxL.resize(Lmax+1, 1);
	maxR.resize(Lmax+1, 1);

	for (int hop=2; hop<Lmax+1; ++hop){
		for (int i=0; i<v2Middle.size(); ++i){

			unsigned hop1 = v2Middle[i].lp.size()-1, vv = v2Middle[i].lp[hop1];
			if (hop1+hop <= Lmax){
				maxL[hop] = max(v2space_Reverse[v2p[vv]][hop], maxL[hop]);
			}

			hop1 = v2Middle[i].rp.size()-1, vv = v2Middle[i].rp[hop1];
			if (hop1+hop <= Rmax){
				maxR[hop] = max(v2space[v2p[vv]][hop], maxR[hop]);
			}
		}
	}

	Join_initial();
	int ss = 0;

	omp_set_num_threads(threads);
	double g = omp_get_wtime(); // omp设立时间点

	#pragma omp parallel
	{
		int pid = omp_get_thread_num(), np = omp_get_num_threads();

		for (int u=pid; u<v2Middle.size(); u+=np){
			// 中间路径存储在对应的中间点

			long long sss = 0, total1=0, total2=0;
			vector<long long> s1(Lmax+1),
							  s2(Lmax+1);

			vector<unsigned>& elems = Elems[pid],
							& flag_ = Flag_[pid];


			vector<vector<pth> >& L_paths = Lpaths[pid],
								& R_paths = Rpaths[pid];


			vector<unsigned> & l1 = v2Middle[u].lp, & r1 = v2Middle[u].rp; // 尾点

			double t1 = omp_get_wtime(); // omp设立时间点

			unsigned vv1 = l1[l1.size()-1];
			unsigned vv2 = r1[r1.size()-1];

			// 现有数据直接赋值为1
			for(int k=0; k<l1.size(); ++k){
				flag_[v2p[l1[k]]] = 1;
			}
			for(int k=0; k<r1.size(); ++k){
				flag_[v2p[r1[k]]] = 1;
			}


			if (vv1 == src){ // 不需要再遍历，直接添加
				L_paths[l1.size()-1][s1[l1.size()-1]]=l1; //make_pair(lens, );
				s1[l1.size()-1] += 1;
			}else{
				l1.pop_back();
				flag_[v2p[dst]] = 1;
				DFS_Join(vv1, src, Lmax, flag_, l1, 0, L_paths, s1);
				flag_[v2p[dst]] = 0;
			}

			if (vv2 == dst){
				R_paths[r1.size()-1][s2[r1.size()-1]]=r1;
				s2[r1.size()-1] += 1;
			}else{
				r1.pop_back();
				flag_[v2p[src]] = 1;
				DFS_Join(vv2, dst, Rmax, flag_, r1, 1, R_paths, s2);
				flag_[v2p[src]] = 0;
			}


			double t2 = omp_get_wtime(); // omp设立时间点

			long long sum1 = accumulate(s1.begin(), s1.end(), 0),
					  sum2 = accumulate(s2.begin(), s2.end(), 0);

			if (sum1 < sum2)
				PathJoin(L_paths, R_paths, elems, s1, s2, sss);
			else
				PathJoin_R(L_paths, R_paths, elems, s1, s2, sss);

			#pragma omp critical
			{
//				ss += 1;
				totalPath += sss;
			}

			if (totalPath > MaxPaths and global_fff == 0){
				global_fff += 1;
				cout<<"   time: "<<omp_get_wtime()-t111<<endl;
			}


			for(int k=0; k<l1.size(); ++k){
				flag_[v2p[l1[k]]] = 0;
			}
			for(int k=0; k<r1.size(); ++k){
				flag_[v2p[r1[k]]] = 0;
			}
			flag_[v2p[vv1]] = 0;
			flag_[v2p[vv2]] = 0;

			vector<long long>().swap(s1);
			vector<long long>().swap(s2);

//			if (ss % 100000 == 0)
//				cout<<"ss:  "<<ss<<endl;
		}
	}

	cout<<" Join total: "<<totalPath<<"  "<<omp_get_wtime()-g<<" s"<<endl;
	vector<vector<vector<pth> > >().swap(Lpaths);
	vector<vector<vector<pth> > >().swap(Rpaths);
	vector<midd2>().swap(v2Middle);
}


void Zeng_Join(int src, int dst, int numV, int khop){
	cout<<"Threads: "<<threads<<endl;

	int nums=0;
	t111 = omp_get_wtime(); // omp设立时间点
//	double t = omp_get_wtime(); // omp璁剧珛鏃堕棿鐐

	BuildIndex2(src, dst, numV, khop);

	Search_Space_Join(src, dst, numV, khop);

	MiddlePart(src, dst, numV, khop);

}



//// ======= HybridEnum ======



int ifvisit(int tree_id, int id, unordered_map<int, PTnode>& TreeMap){ // 杈撳叆涓  鍙跺瓙鑺傜偣 鍜  褰撳墠瑕佸垽鏂殑id
	PTnode& node = TreeMap[tree_id];
	int graphid = node.id;
	int parentid = -1;

	if (id == graphid)
		return 1; // 宸茬粡璁块棶

	parentid = node.parent; // 杩樻槸鏍戠殑id

	while (1){

		if (parentid == -1) // 鍥炴函鍒版牴鑺傜偣鑲畾涓 -1锛
			break;

		PTnode& parent = TreeMap[parentid];
		if (parent.id == id)
			return 1;
		else
			parentid = parent.parent;
	}

	return 0;
}


void printTreePath(int tree_id, unordered_map<int, PTnode>& TreeMap, int fff, int place){
	// fff
	vector<int> vv;
	if (fff == 1)
		vv.push_back(dst);
	while (1){
		PTnode & node = TreeMap[tree_id];
		vv.push_back(node.id);

		tree_id = node.parent;
		if (tree_id == -1){
			break;
		}
	}


	for (int ii=0; ii<vv.size(); ii++)
		cout<<vv[vv.size()-ii-1]<<" ";
	cout<<endl;
}


void WriteTreePath(int tree_id, int dd, unordered_map<int, PTnode>& TreeMap, int fff, int place, int ff){
	vector<unsigned> vv;
	if (fff == 1)
		vv.push_back(dd);

	while (1){
		PTnode & node = TreeMap[tree_id];
		vv.push_back(node.id);

		tree_id = node.parent;
		if (tree_id == -1){
			break;
		}
	}

	if (ff > 0){
		P_thread[place][vv.size()-1].push_back(vv);
	}else{ //
		P_R_thread[place][vv.size()-1].push_back(vv);
	}
}


int NearestValue(int tree_id, int id, unordered_map<int, PTnode>& TreeMap){
	int parentid = -1;
	PTnode& node = TreeMap[tree_id];
	if (node.pt.find(id) != node.pt.end()){
		return node.pt[id];
	}

	parentid = node.parent; // 杩樻槸鏍戠殑id
	while (1){
		if (parentid == -1) // 鍥炴函鍒版牴鑺傜偣鑲畾涓 -1锛
			break;

		PTnode& parent = TreeMap[parentid];
		if (parent.pt.find(id) != parent.pt.end())
			return parent.pt[id];
		else
			parentid = parent.parent;
	}

	return 0;
}


void BrachInitial(int src, int dst, int numV, int khop){
	t111 = omp_get_wtime();
	double tt1 = omp_get_wtime();
	PTnode root(src, 3, -1, 1, 0);
	vector<PTnode> bch;
	bch.push_back(root);
	unordered_map<int, int> flag;
	flag[src] = 1;

	set<int> dst_Neig;
	for (int ij=0; ij<con[dst].size(); ++ij)
		dst_Neig.insert(con[dst][ij]);

	// 鍩轰簬bfs鍒嗗竷锛岀敓鎴愪竴浜涜绠楀垎鏀
	for (int i=0; i<con[src].size(); ++i){
		int v = con[src][i];

		if (v == dst)
			totalPath += 1;
		else if(flag[v] == 0){
			flag[v] = 1;
			PTnode next(v, 1, 1, 0, 1);
			bch.push_back(next);
			Branches.push_back(bch);
//			for (int j=0; j<con[v].size(); ++j){
//				int u = con[v][j];
//
//				if (u == dst)
//					totalPath += 1; // 鑾峰緱璺緞
//				else if(flag[u] == 0){
//					flag[u] = 1;
//					PTnode next(u, 1, 2, 0, 2);
//					bch.push_back(next);
//					Branches.push_back(bch);
//					bch.pop_back();
//					flag[u] = 0;
//				}else{
//
//				}
//			}

			bch.pop_back();
			flag[v] = 0;
		}else{

		}
	}


//	vector<unordered_map<int, PTnode> > TreeMapList(threads);
	int totalSize = Branches.size();


	omp_set_num_threads(threads);
	#pragma omp parallel // 绾︽潫鑼冨洿鍐呯殑椤剁偣瀹屾垚    PrunExt 鎿嶄綔
	{
		int pid = omp_get_thread_num(), np = omp_get_num_threads();

		for (int u=pid; u<totalSize; u+=np){
			int treeid_pid = 0, cnt1 = 0; //鏍慽d
			vector<PTnode>& bchOne = Branches[u];
			vector<int> treelist_pid;
			unordered_map<int, PTnode> TreeMap; // 鑾峰緱涓 涓猅reeMap

			// 瀹屽杽鍥
			for (int i=0; i<bchOne.size(); ++i){
				bchOne[i].child = i==bchOne.size()-1? 1:0; // 鍗曟潯閾
				bchOne[i].state = i==bchOne.size()-1? 1:5;
				bchOne[i].parent = i==0? -1:treeid_pid-1;
				TreeMap[treeid_pid] = bchOne[i];
				treelist_pid.push_back(treeid_pid);
				treeid_pid += 1; // 鏇存柊
			}


			while(1){

				for (int i=0; i<treelist_pid.size(); i++){
					int active_treeid = treelist_pid[i];
					PTnode & node = TreeMap[active_treeid]; // 鍙栧埌褰撳墠璁块棶鐨勬爲鑺傜偣
					if (cnt1 >= delta or node.state != 1){ // 闄愬埗鏁伴噺鍜岃妭鐐圭殑璁块棶鐘舵
						continue;
					}

					int fflag = -1;
					int level = node.level; // 褰撳墠鑺傜偣鐨刲evel
					if (level == khop - 1){ // 娌￠棶棰
						node.pt[node.id] = 2, node.state = 2;
						if (dst_Neig.find(node.id) != dst_Neig.end()){
							#pragma omp critical
							{
								totalPath += 1;
							}
//							printTreePath(active_treeid, TreeMap, 1, pid);
							if (totalPath > MaxPaths and global_fff == 0){
								global_fff += 1;
								cout<<totalPath<<"   time: "<<omp_get_wtime()-t111<<endl;
							}
						}
						continue;
					}

					int graphid = node.id;


					for (int ij=0; ij<con[graphid].size(); ++ij){
						int neigid = con[graphid][ij];

						if (neigid == src or neigid == bchOne[1].id) continue;

						int flag = ifvisit(active_treeid, neigid, TreeMap); // 閫氳繃鍥炴函鐨勬柟寮忛亶鍘嗘暣鏉¤矾寰
						if (flag == 1)
							continue; // 璇ラ偦灞呯偣宸茬粡琚闂簡

//						cout<<graphid<<"  "<<neigid<<endl;
						if ( neigid == dst ){
							#pragma omp critical
							{
								totalPath += 1;
							}

							// parent涓噰鐢ㄧ殑鏄爲鑺傜偣鐨刬d
							PTnode tail(dst, 2, active_treeid, 0, level+1); // 浠rc涓哄熀鍒涘缓鏍硅妭鐐
							tail.pt[dst] = 1, fflag = 1; //
							TreeMap[treeid_pid] = tail;
							node.child += 1; // 姣忓涓 涓偦灞呯偣锛屽氨澶氫竴涓猚hild
//								printTreePath(treeid_pid, TreeMap, 0);
							treeid_pid += 1; // 鏇存柊


						}else{

							int value = NearestValue(active_treeid, neigid, TreeMap); // 浠巔t閲岄潰鎵句竴涓《鐐

							if ( value + level + 1 <= khop){
								PTnode next(neigid, 3, active_treeid, 0, level+1); // 浠rc涓哄熀鍒涘缓鏍硅妭鐐
								TreeMap[treeid_pid] = next;
								node.child += 1; // 姣忓涓 涓偦灞呯偣锛屽氨澶氫竴涓猚hild
								fflag = 1;
								treeid_pid += 1; // 閬垮厤id鍐茬獊
							}
						}
					}


					if (fflag == -1){ // 纭鏈夋棤鏂板姞椤剁偣
						node.state = 2;
						node.pt[node.id] = khop + 1 - node.level;
						node.dis[node.id] = 0; // 璁板綍鏈 鐭窛绂
					}else{
						node.state = 5;
					}

					cnt1 += 1;
				}
				cnt1 = 0;

				// 鍙嶅悜鏇存柊
				vector<int>().swap(treelist_pid);
				for (auto it=TreeMap.begin(); it!=TreeMap.end(); ++it){
					treelist_pid.push_back(it->first);
				}


				for (int i=0; i<treelist_pid.size(); i++){
					int active_treeid = treelist_pid[i];
					PTnode & node = TreeMap[active_treeid]; // 鍙栧埌褰撳墠璁块棶鐨勬爲鑺傜偣

					if (node.state != 2) continue; // 鍙鐘舵 佷负CLOSED鐨勯《鐐硅繘琛屾搷浣

					int parent = node.parent;
					if (node.pt[node.id] + node.level < khop){
						for (auto it=node.pt.begin(); it!=node.pt.end(); ++it){
							int id = it->first; // id涓烘爲鑺傜偣鐨刬d
							if (it->second > node.pt[node.id] + node.dis[id]){
								it->second = node.pt[node.id] + node.dis[id];
							}
						}
					}

					PTnode & Pnode = TreeMap[parent]; // 鍙栧埌褰撳墠璁块棶鑺傜偣鐨勭埗浜茶妭鐐
					Pnode.dis[Pnode.id] = 0; // 鑷韩璺濈鍒濆鍖

					if (Pnode.pt[Pnode.id] == 0 or Pnode.pt[Pnode.id] > node.pt[node.id]+1){
						Pnode.pt[Pnode.id] = node.pt[node.id] + 1;
					}

					for (auto it=node.pt.begin(); it!=node.pt.end(); ++it){
						int tid = it->first;
						if (Pnode.pt.find(tid) != Pnode.pt.end()){
							// 宸茬粡灞炰簬 Pnode锛屽垯涓嶇敤鏇存柊dis
							Pnode.pt[tid] = Pnode.pt[tid]>node.pt[tid]? Pnode.pt[tid]:node.pt[tid];
						}else{
							Pnode.pt[tid] = node.pt[tid];
						}
						Pnode.dis[tid] = node.dis[tid] + 1; // 鏈 鐭窛绂荤殑杩唬鏇存柊
					}

					TreeMap.erase(active_treeid);
//					cout<<"delete:  "<<node.id<<endl;
					Pnode.child -= 1;
					if (Pnode.child == 0){
//						cout<<"  child: "<<Pnode.id<<endl;
						Pnode.state = 2; // 閲嶇疆涓篊LOSED
					}

				}

				vector<int>().swap(treelist_pid);
				for (auto it=TreeMap.begin(); it!=TreeMap.end(); ++it){
					treelist_pid.push_back(it->first);
				}
				maxlevel = 0;

				for (int i=0; i<treelist_pid.size(); ++i){
					int active_treeid = treelist_pid[i];
					PTnode & node = TreeMap[active_treeid]; // 鍙栧埌褰撳墠璁块棶鐨勬爲鑺傜偣

					if (maxlevel < node.level)
						maxlevel = node.level;
				}

				for (int i=0; i<treelist_pid.size(); ++i){
					int active_treeid = treelist_pid[i];
					PTnode & node = TreeMap[active_treeid]; // 鍙栧埌褰撳墠璁块棶鐨勬爲鑺傜偣

					if (node.child == 0 and node.level == maxlevel and node.state != 2){
						node.state = 1;
					}

					if (node.child == 0 and node.level == maxlevel-1 and node.state != 2)
						node.state = 3;
				}

				if (maxlevel <= 1){ // 涓嶅瓨鍦ㄩ《鐐逛簡
					cout<<u<<"   "<<totalSize<<"   Paths:  "<<totalPath<<endl;
					break;
				}
			}
			TreeMap.clear();
		}


	}

	cout<<"Paths:  "<<totalPath<<endl;
}


void BrachJoin(int src, int dst, int numV, int khop, int ppid, int ff){
	PTnode root(src, 3, -1, 1, 0);
	vector<vector<PTnode> > BranchesJoin;
	vector<PTnode> bch;
	bch.push_back(root);
	unordered_map<int, int> flag;
	flag[src] = 1;

	set<int> dst_Neig;
	for (int ij=0; ij<con[dst].size(); ++ij)
		dst_Neig.insert(con[dst][ij]);

	// 鍩轰簬bfs鍒嗗竷锛岀敓鎴愪竴浜涜绠楀垎鏀
	for (int i=0; i<con[src].size(); ++i){
		int v = con[src][i];

		if(flag[v] == 0){
			flag[v] = 1;
			PTnode next(v, 1, 1, 0, 1);
			bch.push_back(next);
			BranchesJoin.push_back(bch);
			bch.pop_back();
			flag[v] = 0;
		}else{

		}
	}


	int totalSize = BranchesJoin.size();
	for (int u=0; u<totalSize; u+=1){
		int treeid_pid = 0, cnt1 = 0; //鏍慽d
		vector<PTnode>& bchOne = BranchesJoin[u];
		vector<int> treelist_pid;
		unordered_map<int, PTnode> TreeMap; // 鑾峰緱涓 涓猅reeMap

		// 瀹屽杽鍥
		if (bchOne[bchOne.size()-1].id == dst){
			vector<unsigned> aa;
			aa.push_back(src), aa.push_back(dst);
			if (ff > 0){
				P_thread[ppid][1].push_back(aa);
			}else{ //
				P_R_thread[ppid][1].push_back(aa);
			}
			continue;
		}

		for (int i=0; i<bchOne.size(); ++i){
			bchOne[i].child = i==bchOne.size()-1? 1:0; // 鍗曟潯閾
			bchOne[i].state = i==bchOne.size()-1? 1:5;
			bchOne[i].parent = i==0? -1:treeid_pid-1;
			TreeMap[treeid_pid] = bchOne[i];
			treelist_pid.push_back(treeid_pid);
			treeid_pid += 1; // 鏇存柊
		}


		while(1){

			for (int i=0; i<treelist_pid.size(); i++){
				int active_treeid = treelist_pid[i];
				PTnode & node = TreeMap[active_treeid]; // 鍙栧埌褰撳墠璁块棶鐨勬爲鑺傜偣
				if (cnt1 >= delta or node.state != 1){ // 闄愬埗鏁伴噺鍜岃妭鐐圭殑璁块棶鐘舵
					continue;
				}

				int fflag = -1;
				int level = node.level; // 褰撳墠鑺傜偣鐨刲evel
				if (level == khop - 1){ // 娌￠棶棰
					node.pt[node.id] = 2, node.state = 2;
					if (dst_Neig.find(node.id) != dst_Neig.end()){
						WriteTreePath(active_treeid, dst, TreeMap, 1, ppid, ff);
					}
					continue;
				}

				int graphid = node.id;


				for (int ij=0; ij<con[graphid].size(); ++ij){
					int neigid = con[graphid][ij];

					if (neigid == src or neigid == bchOne[1].id) continue;

					int flag = ifvisit(active_treeid, neigid, TreeMap); // 閫氳繃鍥炴函鐨勬柟寮忛亶鍘嗘暣鏉¤矾寰
					if (flag == 1)
						continue; // 璇ラ偦灞呯偣宸茬粡琚闂簡

//						cout<<graphid<<"  "<<neigid<<endl;
					if ( neigid == dst ){
						// parent涓噰鐢ㄧ殑鏄爲鑺傜偣鐨刬d
						PTnode tail(dst, 2, active_treeid, 0, level+1); // 浠rc涓哄熀鍒涘缓鏍硅妭鐐
						tail.pt[dst] = 1, fflag = 1; //
						TreeMap[treeid_pid] = tail;
						node.child += 1; // 姣忓涓 涓偦灞呯偣锛屽氨澶氫竴涓猚hild
						WriteTreePath(treeid_pid, dst, TreeMap, 0, ppid, ff);
						treeid_pid += 1; // 鏇存柊


					}else{

						int value = 0; // NearestValue(active_treeid, neigid, TreeMap); // 浠巔t閲岄潰鎵句竴涓《鐐

						if ( value + level + 1 <= khop){
							PTnode next(neigid, 3, active_treeid, 0, level+1); // 浠rc涓哄熀鍒涘缓鏍硅妭鐐
							TreeMap[treeid_pid] = next;
							node.child += 1; // 姣忓涓 涓偦灞呯偣锛屽氨澶氫竴涓猚hild
							fflag = 1;
							treeid_pid += 1; // 閬垮厤id鍐茬獊
						}
					}
				}


				if (fflag == -1){ // 纭鏈夋棤鏂板姞椤剁偣
					node.state = 2;
					node.pt[node.id] = khop + 1 - node.level;
					node.dis[node.id] = 0; // 璁板綍鏈 鐭窛绂
				}else{
					node.state = 5;
				}

				cnt1 += 1;
			}
			cnt1 = 0;

			// 鍙嶅悜鏇存柊
			vector<int>().swap(treelist_pid);
			for (auto it=TreeMap.begin(); it!=TreeMap.end(); ++it){
				treelist_pid.push_back(it->first);
			}


			for (int i=0; i<treelist_pid.size(); i++){
				int active_treeid = treelist_pid[i];
				PTnode & node = TreeMap[active_treeid]; // 鍙栧埌褰撳墠璁块棶鐨勬爲鑺傜偣

				if (node.state != 2) continue; // 鍙鐘舵 佷负CLOSED鐨勯《鐐硅繘琛屾搷浣

				int parent = node.parent;
				if (node.pt[node.id] + node.level < khop){
					for (auto it=node.pt.begin(); it!=node.pt.end(); ++it){
						int id = it->first; // id涓烘爲鑺傜偣鐨刬d
						if (it->second > node.pt[node.id] + node.dis[id]){
							it->second = node.pt[node.id] + node.dis[id];
						}
					}
				}

				PTnode & Pnode = TreeMap[parent]; // 鍙栧埌褰撳墠璁块棶鑺傜偣鐨勭埗浜茶妭鐐
				Pnode.dis[Pnode.id] = 0; // 鑷韩璺濈鍒濆鍖

				if (Pnode.pt[Pnode.id] == 0 or Pnode.pt[Pnode.id] > node.pt[node.id]+1){
					Pnode.pt[Pnode.id] = node.pt[node.id] + 1;
				}

				for (auto it=node.pt.begin(); it!=node.pt.end(); ++it){
					int tid = it->first;
					if (Pnode.pt.find(tid) != Pnode.pt.end()){
						// 宸茬粡灞炰簬 Pnode锛屽垯涓嶇敤鏇存柊dis
						Pnode.pt[tid] = Pnode.pt[tid]>node.pt[tid]? Pnode.pt[tid]:node.pt[tid];
					}else{
						Pnode.pt[tid] = node.pt[tid];
					}
					Pnode.dis[tid] = node.dis[tid] + 1; // 鏈 鐭窛绂荤殑杩唬鏇存柊
				}

				TreeMap.erase(active_treeid);
//					cout<<"delete:  "<<node.id<<endl;
				Pnode.child -= 1;
				if (Pnode.child == 0){
//						cout<<"  child: "<<Pnode.id<<endl;
					Pnode.state = 2; // 閲嶇疆涓篊LOSED
				}

			}

			vector<int>().swap(treelist_pid);
			for (auto it=TreeMap.begin(); it!=TreeMap.end(); ++it){
				treelist_pid.push_back(it->first);
			}
			maxlevel = 0;

			for (int i=0; i<treelist_pid.size(); ++i){
				int active_treeid = treelist_pid[i];
				PTnode & node = TreeMap[active_treeid]; // 鍙栧埌褰撳墠璁块棶鐨勬爲鑺傜偣

				if (maxlevel < node.level)
					maxlevel = node.level;
			}

			for (int i=0; i<treelist_pid.size(); ++i){
				int active_treeid = treelist_pid[i];
				PTnode & node = TreeMap[active_treeid]; // 鍙栧埌褰撳墠璁块棶鐨勬爲鑺傜偣

				if (node.child == 0 and node.level == maxlevel and node.state != 2){
					node.state = 1;
				}

				if (node.child == 0 and node.level == maxlevel-1 and node.state != 2)
					node.state = 3;
			}

			if (maxlevel <= 1){ // 涓嶅瓨鍦ㄩ《鐐逛簡
//				cout<<u<<"   "<<totalSize<<"   Paths:  "<<totalPath<<endl;
				break;
			}
		}
		TreeMap.clear();
	}

	vector<vector<PTnode> >().swap(BranchesJoin);
}



void HybridEnum(int src, int dst, int numV, int khop){
	// 鍒涘缓鏍硅妭鐐

	BrachInitial(src, dst, numV, khop);
}



void HybridEnum_Plus(int src, int dst, int numV, int khop){
	// 瀵绘壘涓棿鑺傜偣
	t111 = omp_get_wtime();
	BuildIndex2(src, dst, numV, khop);

	unsigned Lhop=1, Rhop=1;
	Search_Space_Join(src, dst, numV, khop);
	initial_parameters(src, dst, Lmax, Rmax);

	while (1){
		// .first=Lhop鐨勭偣鍏堟洿鏂
		vector<unsigned> L_(active_nums, -1000), R_(active_nums, -1000);

		for (int i=0; i<numV; i++){
			if (v2p[i] == -1)
				continue;

			int left = disL_[v2p[i]];

			if (left == Lhop){ // 琛ㄧず鍦ㄨ鎯呭喌涓嬶紝椤剁偣灞炰簬 left+right hop 鐨勪腑闂磋矾寰
				for (int ii=0; ii<con[i].size(); ++ii){
					unsigned v_ = con[i][ii];

					if (v2p[v_] == -1) continue;

					if (v_ == src || v_ == dst) continue;

					L_[v2p[v_]] = Lhop+1;

					if (L_[v2p[v_]] == disR_[v2p[v_ ]]+1){

						if (MFlag_Left[v2p[v_]][L_[v2p[v_]]] == 0){ // 璁板綍涓 涓嬪湪Lhop澶勭殑棰勬祴璺緞鏁伴噺
							MFlag_Left[v2p[v_]][L_[v2p[v_]]] = 1;
							path_src[v2p[v_]] += (v2space_Reverse[v2p[v_]][ L_[v2p[v_]] ] * 1); // L_[v2p[v_]]
						}

						if (MFlag_Right[v2p[v_]][disR_[v2p[v_ ]]] == 0){
							MFlag_Right[v2p[v_]][disR_[v2p[v_ ]]] = 1;
							path_dst[v2p[v_]] += (v2space[v2p[v_]][ disR_[v2p[v_]] ] * 1); // disR_[v2p[v_]]
						}
					}
				}
			}
		}

		disL_.swap(L_); // 鍏ㄩ儴鏇挎崲
		Lhop += 1;

		if (Lhop + Rhop == khop) {
			vector<unsigned>().swap(disL_);
			vector<unsigned>().swap(disR_);
			break;
		}

		for (int i=0; i<numV; i++){
			if (v2p[i] == -1) continue;

			int right = disR_[v2p[i]];

			if (right == Rhop){ // 琛ㄧず鍦ㄨ鎯呭喌涓嬶紝椤剁偣灞炰簬 left+right hop 鐨勪腑闂磋矾寰
				for (int ii=0; ii<con[i].size(); ++ii){
					unsigned v_ = con[i][ii];
					if (v2p[v_] == -1)
						continue;

					if (v_ == src || v_ == dst) continue;

					R_[v2p[v_]] = Rhop+1;
					if (disL_[v2p[v_ ]] == R_[v2p[v_]]){

						if (MFlag_Left[v2p[v_]][disL_[v2p[v_ ]]] == 0){ // 璁板綍涓 涓嬪湪Lhop澶勭殑棰勬祴璺緞鏁伴噺
							MFlag_Left[v2p[v_]][disL_[v2p[v_ ]]] = 1;
							path_src[v2p[v_]] += (v2space_Reverse[v2p[v_]][ disL_[v2p[v_ ]] ] * 1); // disL_[v2p[v_ ]]
						}

						if (MFlag_Right[v2p[v_]][R_[v2p[v_]]] == 0){
							MFlag_Right[v2p[v_]][R_[v2p[v_]]] = 1;
							path_dst[v2p[v_]] += (v2space[v2p[v_]][ R_[v2p[v_]] ] * 1); // R_[v2p[v_]]
						}
					}
				}
			}
		}

		disR_.swap(R_); // 鍏ㄩ儴鏇挎崲
		Rhop += 1;
		if (Lhop + Rhop == khop) {
			vector<unsigned>().swap(disL_);
			vector<unsigned>().swap(disR_);
			break;
		}
	}

	vector<unsigned> middle; // numV
	for (int i=0; i<numV; ++i){
		if (v2p[i] == -1)
			continue;
		if (path_src[v2p[i]] == 0 and path_dst[v2p[i]] == 0)
			continue;
		// 纭涓棿鐐圭殑闆嗗悎涓簃iddle
		middle.push_back(i);
	}

	P_thread.resize(threads), P_R_thread.resize(threads);
	int totalSize = middle.size();

	omp_set_num_threads(threads);
	#pragma omp parallel // 绾︽潫鑼冨洿鍐呯殑椤剁偣瀹屾垚    PrunExt 鎿嶄綔
	{
		int pid = omp_get_thread_num(), np = omp_get_num_threads();

		for (int u=pid; u<totalSize; u+=np){
			// 鍒╃敤HybridEnum鏉ヨ幏寰楄矾寰勶紝骞跺垎鍒瓨鍌ㄥ埌
			unsigned mid = middle[u];
			BrachJoin(mid, src, numV, Lmax, pid, 1); // 鍗曚釜绾跨▼锛屽苟瑕佸啓鍏ュ埌鐭╅樀涓
			BrachJoin(mid, dst, numV, Rmax, pid, 0); // 鍗曚釜绾跨▼锛屽苟瑕佸啓鍏ュ埌鐭╅樀涓

			// === 鎵ц鎷兼帴绋嬪簭  ===
			unordered_map<int, int> eles;

			for (auto it=P_thread[pid].begin(); it!=P_thread[pid].end(); ++it){
				int size1 = it->first;
				vector<vector<unsigned> >& lpath = it->second;

//				cout<<"   mid:"<<mid<<"  l: "<<lpath.size()<<endl;

				for (int ii=0; ii<lpath.size(); ++ii){
					vector<unsigned>& lp1 = lpath[ii];
					for (int ij=0; ij<lp1.size()-1; ij++){
//						cout<<lp1[ij]<<"  ";
						eles[lp1[ij]] = 1;
					}
//					cout<<endl;

					for (int ic = 0; ic < 2; ++ic){
						int size2 = ic==0? size1:size1-1;
						vector<vector<unsigned> >& rpath = P_R_thread[pid][size2];

						for (int jj=0; jj<rpath.size(); ++jj){
							int ffg = 1;
							vector<unsigned>& rp1 = rpath[jj];
							for (int jk=0; jk<rp1.size()-1; jk++){
//								cout<<"   "<<rp1[jk]<<"  ";
								if (eles[rp1[jk]] == 1){
									ffg = -1;
									break; // 鏈夐噸澶嶉《鐐
								}
							}
//							cout<<" &&& "<<ffg<<endl;
							if (ffg == 1){
								#pragma omp critical
								{
									totalPath += 1;
								}
								if (totalPath > MaxPaths and global_fff == 0){
									global_fff += 1;
									cout<<totalPath<<"   time: "<<omp_get_wtime()-t111<<endl;
								}
							}
						}
					}

					eles.clear();
				}
			}

			// ================
			P_thread[pid].clear();
			P_R_thread[pid].clear();
		}
	}

	cout<<"Paths:  "<<totalPath<<endl;
}




int main(){

	numV = 100000000, khop = 6;
	aplace = 0, bplace = 5001;

// aplace = 1000, bplace = 10000000;
	threads = 1;
	int ff = 4;
	delta = 10;

	initial2(numV, ff); // 1
	cout<<"a: "<<aplace<<"  b: "<<bplace<<endl;
	cout<<"Khop: "<<khop<<"   Method: "<<ff<<endl;

	double t = omp_get_wtime();
	if (ff == 1){
		Sun_DFS(src, dst, numV, khop);
//		HybridEnum(src, dst, numV, khop);
	} else if(ff == 2){
		Sun_Join(src, dst, numV, khop);
		//		HybridEnum_Plus(src, dst, numV, khop);
	} else if (ff == 3){
		Zeng_Baseline(src, dst, numV, khop);
	} else{
		Zeng_Join(src, dst, numV, khop);
	}
	double ttt = omp_get_wtime()-t;
	cout<<"time:  "<<ttt<<"  s"<<endl;

	string new_filename = "SJ_4_6_1SINGLE.txt";
	const char *file = new_filename.c_str();
	fstream outfileX;
	outfileX.open(file, ios::out);
	outfileX<<ff<<endl;
	outfileX<<ttt<<endl;
	outfileX<<totalPath<<endl;


//	srand((unsigned)time(NULL));
//
//	int n = 10000000, m = 1000000000; // cacheline的行数
//	vector<int> line2place; // 每个cacheline行对应的位置
//	vector<int> elem, ff;
//	int cache_miss = 0;
//	line2place.resize(m, -1);
//	ff.resize(m, 0);
//
//	for (int i=0; i<m; i++)
//		elem.push_back(rand()%m);
//
//	double t = omp_get_wtime();
//
//	for (int i=0; i<elem.size(); ++i){
//		int line_num = elem[i];
//		int p = line2place[line_num];
//		if ( p == -1 or i-p > n )
//			cache_miss += 1;
//
//		line2place[line_num] = i;
//	}
//
//	double tt = omp_get_wtime();
//	cout<<"time: "<<tt-t<<" s"<<endl;
//	cout<<"miss: "<<cache_miss<<endl;
//
//	return 0;


//	srand((unsigned)time(NULL));
//
//	int n = 1000000, m = 160000000; // cacheline的行数
//	vector<int> line2place; // 每个cacheline行对应的位置
//	vector<int> elem, ff;
//	int cache_miss = 0, cnt = 0;
//	line2place.resize(m, -1);
//	ff.resize(m, 0);
//
//	for (int i=0; i<m; i++)
//		elem.push_back(rand()%(m/16));
//
//	double t = omp_get_wtime();
//
//	for (int i=0; i<elem.size(); ++i){
//		int line_num = elem[i];
//		int p = line2place[line_num];
//		if ( p == -1){
//			cache_miss += 1;
//		}else{
////			cout<<"len: "<<i-p<<endl;
//			if (i-p > n ){
//				for (int j=p+1; j<i; ++j){
//					if (ff[j] == 0){
//						cnt += 1;
//						ff[j] = 1;
//					}
//				}
//				if (cnt > n)
//					cache_miss += 1;
//				ff.clear();
//				cnt = 0;
//			}
//		}
//
//		line2place[line_num] = i;
//	}
//
//	double tt = omp_get_wtime();
//	cout<<"time: "<<tt-t<<" s"<<endl;
//	cout<<"miss: "<<cache_miss<<endl;


	return 0;
}

