#ifndef _SAT_H_
#define _SAT_H_

#define UNASSIGNED 0
#define NO_ANTEC -1

#define NULL_CLAUSE 0
#define COULD_ADD 1
#define USELESS_CLAUSE 2
#define TOO_LARGE 3

#define ALREADY_ASSIGNED_SAME 2
#define SUCCESSFULLY_ASSIGNED 1
#define CONFLICT 0

#define RESOLVE_LIMIT 100
#define LEARNT_SIZE_HARD_LIMIT 6
#define N_CONFLICT_TO_RESTART_HARD_LIMIT 65535
#define DENOMINATOR_HARD_LIMIT 1024

#define SAT 1
#define UNSAT 0
#define NOT_YET 2

using namespace std;

struct var_info {
  int value;
  int score;
  // the following three only valid when value not UNASSIGNED
  int level;
  int antec; // NO_ANTEC means it's a decision
  int order;
  vector<int> pos_vec;
  vector<int> neg_vec;
  var_info():value(UNASSIGNED), score(0){;};
};

struct twoidx {
  int idx1;
  int idx2;
  twoidx():idx1(0),idx2(1){;}
  twoidx(int a, int b):idx1(a),idx2(b){;}
};

struct var_score {
  int var;
  int *score;
  var_score(int v, int *s):var(v),score(s){;}
};

struct assignment {
  int value;
  int level;
  int antec;
  assignment(int v, int l, int a):value(v),level(l),antec(a){;}
};

class sat {
public:
  sat(vector<vector<int> >&, int, int, int, int, int, int);
  void get_learnt_clause(vector<vector<int> > &);
  bool solve();
  int thread_learn(int, bool *);
  void write_result_file(char *);
private:
  bool _verify();
  static bool _score_cmp(var_score &vs1, var_score &vs2){
    return *vs1.score > *vs2.score;
  }
  void _init();
  void _init_var_info();
  void _init_watch();
  void _init_to_assign_with_var_info();
  void _simulated_annealing();

  /* fill bcp clause */
  bool _assign_handler(int, int, int, vector<int> &);
  int _try_assign(int, int, int);
  void _assign(int, int, int);

  bool _preproc();
  void _fill_len_1_clause(vector<int> &);
  void _fill_1_phase_var(vector<int> &);

  bool _branch_get_bcp_clause(vector<int> &);
  void _update_watch(vector<int> &);
  bool _try_move_watch(int *, int *, vector<int> &);
  bool _bcp(vector<int> &, int &, int &);
  bool _has_decision();
  int _analyze_conflict(int, int, bool &, vector<int> &);
  bool _try_find_1uip(vector<int> &);
  void _resolve(vector<int> &, int, int);
  int _find_back_level(vector<int> &);
  int _check_learnt_clause(vector<int> &);
  void _add_learnt_clause(vector<int> &);
  void _backtrack(int, vector<int> &);

  void _restart();
  
  vector<vector<int> > _clause_db;
  vector<twoidx> _watch_db;
  vector<var_info> _var_info_vec;
  deque<assignment> _assign_deque;
  vector<var_score> _to_assign_heap;
  vector<int> _to_assign_vec;

  unsigned int _seed;
  unsigned int _numerator, _denominator;
  int _ori_db_size;
  int _transfered_db_size;
  int _cur_level;
  int _restart_chance;
  int _max_var_idx;
  int _learnt_size_limit;
  int _n_conflict_to_restart;
  int _n_conflict_to_restart_bound;
  bool _has_add_clause;
  
};

struct mt_arg{
  vector<vector<int> > *clause_db;
  int max_var_idx;
  int ori_db_size;
  int restart_chance;
  int numerator;
  int denominator;
  int n_conflict_to_return;
  char *result_file_name;
  pthread_mutex_t *mutex;
  bool time_to_ret;
  mt_arg(
      vector<vector<int> > *c, 
      int m,
      int o,
      int r, 
      int n, 
      int d, 
      int ret,
      char *f,
      pthread_mutex_t *t):
    clause_db(c),
    max_var_idx(m),
    ori_db_size(o),
    restart_chance(r),
    numerator(n),
    denominator(d),
    n_conflict_to_return(ret),
    result_file_name(f),
    mutex(t){;}
};

struct mt_learn_ret{
  int status;
  vector<vector<int> > learnt_clause;
};

void *mt_learn(void *);

void *mt_solve(void *);

struct timespec sat_start_time;
struct timespec sat_cur_time;
struct timespec sat_end_time;

double diff_time_sec(struct timespec *, struct timespec *);
#endif
