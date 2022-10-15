#include <string>
#include <iostream>
#include <vector>
#include <cmath>
#include <set>
#include <algorithm>
#include <deque>
#include <cmath>

using namespace std;

typedef pair<int, int> pii;
typedef pair<double, bool> pdb;

const double EPS = 1e-9; // for double comparison (epsilon number)

pdb invalid_syntax = pdb(-1, 0);
const double LIMIT = 1e18;
const set<string> symbol_and_func = {"sqrt", "cbrt", "log", "ln", "sin", "cos", "tan", "cot", "+", "-", "*", "/", "^", "%", "!", ".", "(", ")", "0", "1", "2", "3", "4", "5", "6", "7", "8", "9"};
string query;
long long F[20]; // factorial

struct pvb{
	vector<string> operators;
	bool status;

	pvb(vector<string> _operators, bool _status){
		operators = _operators;
		status = _status;
	}

	pvb(){}
};

bool checkCorrectBracketSequence() {
	int cnt = 0;

	for (char x : query) {
		if (x == '(') {
			cnt++;
		}
		else if (x == ')') {
			cnt--;
		}
		if (cnt < 0) {
			return 0;
		}
	}

	return (cnt == 0);
}

vector<vector<int>> children;
vector<pii> brackPos;
vector<int> bracketStartingPoint;

//check if query contains only offline-operable symbols
bool checkMathSymbols() {
	bool check = 1;
	string cur = "";
	for (int i = 0; i < query.size(); i++) {
		if (query[i] == ' '){
			if (! check){
				return 0;
			}
		} else {
			cur += query[i];
			if (symbol_and_func.find(cur) != symbol_and_func.end()) {
				check = 1;
				cur = "";
			} else {
				check = 0;
			}
		}
	}

	return check;
}

double toRadian(double degree){
	return degree * acos(-1.0) / 180;
}

//change +--+9 -> 9 and process special operations like log, trigonometry
pdb processFunc(double result, deque<string> func){
	reverse(func.begin(), func.end());
	for(string f : func){
		if (f == "*" || f == "/" || f == "%" || f == "^" || f == "!"){
			return invalid_syntax;
		}
		if (f == "+"){
			//nothing happens
		} else if (f == "-"){
			result = -result;
		}
		else if (f == "sqrt"){
			if (result < 0){
				return invalid_syntax;
			}
			result = sqrt(result);
		}
		else if (f == "cbrt"){
			result = cbrt(result);
		}
		else if (f == "log"){
			if (result < 0 || abs(result) < EPS){
				return invalid_syntax;
			}
			result = log(result) / log(10);
		} 
		else if (f == "ln"){
			if (result < 0 || abs(result) < EPS){
				return invalid_syntax;
			}
			result = log(result);
		}else {
			bool check = 0; // check = 1 if current result is a non-negative integer divisible by 90
			if (abs(result) >= EPS && abs(result - int(result)) < EPS && int(result) % 90 == 0){
				check = 1;
			}
			result = toRadian(result);
			if (f == "sin"){
				result = sin(result);
			} else if (f == "cos"){
				result = cos(result);
			} else {
				if (check){ // cant apply tan and cot to a non-negative integer divisible by 90
					return invalid_syntax;
				}
				if (f == "tan"){
					result = tan(result);
				} else {
					result = 1 / tan(result);
				}
			}
		}
	}
	return pdb(result, 1);
}

//use dsu because of priority of *, /, %, ^ to update leftmost numbers going with these symbols 
// EXP: expression : 3 + 5 * 2 / 3 - 10
// -> nums = {3, 5, 2, 3, 10}
// first, use dsu to convert nums to {3, 10, 2, 3, 10} (iterate through * first, change nums[1] (5) to 5 * 2) and -> {3, 3.3333 (10 / 3), 2, 3, 10}
// then calculate + and -, and update nums[0], which will be the final result
class DSU{
private:
	vector<int> root;

public:
	void initialize(int num){
		root.clear();
		for(int i = 0; i < num; i++){
			root.push_back(i);
		}
	}

	int getRoot(int x){
		if (root[x] != x){
			root[x] = getRoot(root[x]);
		}
		return root[x];
	}

	void join(int u, int v){
		u = getRoot(u);
		v = getRoot(v);
		if (u > v){
			swap(u, v);
		}
		root[v] = u;
	}
} dsu;

long long Factorial(int n){
	if (F[n] == 0){
		F[0] = 1;
		for(int i = 1; i < 20; i++){
			F[i] = F[i - 1] * i;
		}
	}
	return F[n];
}

pvb processNewOperators(deque<string> &func, vector<double> &nums){
	deque<string> f = {"*"};
	vector<double> n = {35, 3};
	pvb invalid = pvb({}, 0);
	vector<string> operators;
	while (! func.empty() && func.front() == "!"){ // 3!(123) -> 3! * 123 -> 6 * 123
		if (nums.empty()){
			return invalid;
		}
		if (nums.back() < 0 || abs(nums.back() - int(nums.back()) >= EPS) || nums.back() > 19){
			return invalid;
		}
		double num = Factorial(int(nums.back()));
		nums.pop_back();
		nums.push_back(num);
		func.pop_front();
	}
	if (! func.empty()){
		if (func.front().size() == 1){
			if (! nums.empty()){  // EXP: 8 * +--9
				operators.push_back(func.front());
				func.pop_front();
			} 
		} else { // EXP : 8 tan--9
			if (! nums.empty()){
				operators.push_back("*");
			}
		}
	} else {
		// EXP : 3tan9 -> 3 * tan9
		if (! nums.empty()){
			operators.push_back("*");
		}
	}
	return pvb(operators, 1);
}

// returns pair(result, status)
pdb dp(int l, int r){
	//get numbers' positions
	vector<double> nums;
	string cur = "";
	bool decimal_part = 0;
	deque<string> func; // convert to basic math function, e.g. 3 - +- sin90 -> 3 - (-1), first operator will be processed later
	deque<string> operators; // operators of basic function
	string cur_func = "";
	for(int i = l + 1; i <= r; i++){
		if ('0' <= query[i] && query[i] <= '9'){
			cur += query[i];
		} else {
			if (symbol_and_func.find(cur_func) != symbol_and_func.end()){
				if (cur_func != "(" && cur_func != ")"){
					func.push_back(cur_func);
				}
				cur_func = "";
			}
			if (query[i] == '('){
				int pos = bracketStartingPoint[i];
				int S = brackPos[pos].first;
				int T = brackPos[pos].second;
				pdb res = dp(S, T);
				if (res.second == 0){
					return invalid_syntax;
				}
				string res_to_string = to_string(res.first);
				if (count(res_to_string.begin(), res_to_string.end(), '.') != 0){
					while (res_to_string.back() == '0'){
						res_to_string.pop_back();
					}
					if (res_to_string.back() == '.'){
						res_to_string.pop_back();
					}
				}

				if (cur.size() > 18){
					return invalid_syntax;
				}

				//process logarithm
				if (cur != ""){
					if (! func.empty() && func.back() == "log"){
						double num = stod(cur);
						if (abs(num) < EPS || num < 0 || abs(res.first) < EPS || res.first < 0){
							return invalid_syntax;
						}
						func.pop_back();
						res.first = log(res.first) / log(num);
						cur = "";
					}
				}

				if (cur != ""){
					double num = stod(cur);
					// 3(8) or 0.12(0.45), convert to 3 * 8 and 0.12 * 0.45
					if (! decimal_part || count(res_to_string.begin(), res_to_string.end(), '.') != 0){
						pvb process_new_operators_result = processNewOperators(func, nums);
						if (process_new_operators_result.status == 0){
							return invalid_syntax;
						}
						operators.insert(operators.end(), process_new_operators_result.operators.begin(), process_new_operators_result.operators.end());
						pdb process_func_result = processFunc(stod(cur), func);
						if (process_func_result.second == 0){
							return invalid_syntax;
						}
						nums.push_back(process_func_result.first);
						nums.push_back(res.first);
						operators.push_back("*");
					} else {
						int deicimal_point_pos = cur.find('.');
						if (cur.size() - 1 - deicimal_point_pos + res_to_string.size() > 18){
							return invalid_syntax;
						}
						//process recurring decimal
						double numerator = res.first;
						long long denominator = 0;
						for(int i = 0; i < res_to_string.size(); i++){
							denominator *= 10;
							denominator += 9;
						}
						for(int i = 0; i < cur.size() - 1 - deicimal_point_pos; i++){
							denominator *= 10;
						}
						num += numerator / denominator;

						pvb process_new_operators_result = processNewOperators(func, nums);
						if (process_new_operators_result.status == 0){
							return invalid_syntax;
						}
						operators.insert(operators.end(), process_new_operators_result.operators.begin(), process_new_operators_result.operators.end());

						pdb process_func_result = processFunc(num, func);

						if (process_func_result.second == 0){
							return invalid_syntax;
						}

						nums.push_back(process_func_result.first);
					}
					cur = "";
				} else {
					pvb process_new_operators_result = processNewOperators(func, nums);
					if (process_new_operators_result.status == 0){
						return invalid_syntax;
					}
					operators.insert(operators.end(), process_new_operators_result.operators.begin(), process_new_operators_result.operators.end());

					res = processFunc(res.first, func);
					if (res.second == 0){
						return invalid_syntax;
					}
					nums.push_back(res.first);
				}
				func.clear();
				i = T;
				continue;
			}

			if (query[i] == '.'){
				// 3.5.5 -> invalid
				if (decimal_part){
					return invalid_syntax;
				}
				decimal_part = 1;
				if (cur == ""){
					cur += '0';
				}
				cur += '.';
			} else {
				decimal_part = 0;
				if (query[i] != ' '){
					cur_func += query[i];
				}
				if (cur != ""){
					if (cur.back() == '.'){
						cur.pop_back();
					}
					if (cur.size() > 18){
						return invalid_syntax;
					}
					pvb process_new_operators_result = processNewOperators(func, nums);
					if (process_new_operators_result.status == 0){
						return invalid_syntax;
					}
					operators.insert(operators.end(), process_new_operators_result.operators.begin(), process_new_operators_result.operators.end());

					pdb res = processFunc(stod(cur), func);
					if (res.second == 0){
						return invalid_syntax;
					}
					nums.push_back(res.first);
					cur = "";
					func.clear();
				}
			}
		}
	}

	if (nums.empty()){
		return invalid_syntax;
	}

	while (! func.empty() && func.front() == "!"){ // EXP: 3!!
		if (nums.back() < 0 || abs(nums.back() - int(nums.back()) >= EPS) || nums.back() > 19){
			return invalid_syntax;
		}
		double num = Factorial(int(nums.back()));
		nums.pop_back();
		nums.push_back(num);
		func.pop_front();
	}

	if (! func.empty()){
		return invalid_syntax;
	}

	// process to return final result
	dsu.initialize(nums.size());

	// prioritize ^
	for(int i = 0; i < operators.size(); i++){
		if (operators[i] == "^"){
			int rootu = dsu.getRoot(i);
			if (log(LIMIT) / log(nums[rootu]) < nums[i + 1]){
					return invalid_syntax;
				}
			nums[rootu] = pow(nums[rootu], nums[i + 1]);
			dsu.join(i, i + 1);
		}
	}
	
	//proceed to *, /, %
	for(int i = 0; i < operators.size(); i++){
		if (operators[i] == "*" || operators[i] == "/" || operators[i] == "%"){
			int rootu = dsu.getRoot(i);
			if (operators[i] == "*"){
				if (LIMIT / nums[rootu] < nums[i + 1]){
					return invalid_syntax;
				}
				nums[rootu] *= nums[i + 1];
			} else if (operators[i] == "/"){
				if (abs(nums[i + 1]) < EPS){
					return invalid_syntax;
				}
				nums[rootu] /= nums[i + 1];
			} else {
				if (abs(nums[rootu] - int(nums[rootu])) < EPS && abs(nums[i + 1] - int(nums[i + 1])) < EPS){
					nums[rootu] = double(int(nums[rootu]) % int(nums[i + 1]));
				}
			}
			dsu.join(i, i + 1);
		}
	}

	//finally, + and -
	for(int i = 0; i < operators.size(); i++){
		if (operators[i] == "+" || operators[i] == "-"){
			int rootu = dsu.getRoot(i);
			if (operators[i] == "+"){
				if (LIMIT - nums[rootu] < nums[i + 1]){
					return invalid_syntax;
				}
				nums[rootu] += nums[i + 1];
			} else {
				if (nums[i + 1] < 0){
					if (nums[rootu] < 0){
						nums[rootu] -= nums[i + 1];
					} else {
						if (nums[rootu] - LIMIT <= nums[i + 1]){
							nums[rootu] -= nums[i + 1];
						}
					}
				} else {
					if (nums[rootu] > 0){
						nums[rootu] -= nums[i + 1];
					} else {
						if (nums[rootu] + LIMIT >= nums[i + 1]){
							nums[rootu] -= nums[i + 1];
						}
					}
				}
			}
			dsu.join(i, i + 1);
		}
	}

	return pdb(nums[0], 1);
}

string Calculate(string inquiry) {
	brackPos.clear();
	children.clear();
	bracketStartingPoint.clear();
	query = inquiry;
	string invalid = "";

	int limit_len = 1e6;
	if (inquiry.size() > limit_len){
		return invalid;
	}

	// invalid syntax
	if (! checkCorrectBracketSequence() || ! checkMathSymbols()) {
		return invalid;
	}

	// make outer brackets as depth 0
	query = "(" + query + ")";
	bracketStartingPoint = vector<int>(query.size(), -1);

	//create a tree in which inner brackets should be children (lower depth) in the tree
	// e.g ((3 + 5) / 2 - (3 - 4))  2nd and 3rd should be children of 1st opeining bracket in the tree
	vector<int> cur = {0};
	brackPos.push_back({0, query.size() - 1});
	children.resize(count(query.begin(), query.end(), '('));
	bracketStartingPoint[0] = 0;
	
	// total encountered opening brackets
	int total = 0;
	for(int i = 1; i < query.size() - 1; i++){
		if (query[i] == '('){
			total++;
			brackPos.push_back({i, -1});
			bracketStartingPoint[i] = total;
			children[cur.back()].push_back(total);
			cur.push_back(total);
		} else if (query[i] == ')'){
			brackPos[cur.back()].second = i;
			cur.pop_back();
		}
	}

	pdb result = dp(0, query.size() - 1);
	if (result.second == 0){
		return invalid;
	}

	string answer = to_string(result.first);
	if (count(answer.begin(), answer.end(), '.') != 0){
		while (answer.back() == '0'){
			answer.pop_back();
		}
		if (answer.back() == '.'){
			answer.pop_back();
		}
	}
	return answer;
}

int main(){
	cout << Calculate("(3! ^ 2 - tan((40 + 5))) * 3 * 0.(6) / (2 + 1)") << "\n";
}
