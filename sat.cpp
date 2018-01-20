#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <string>
#include <algorithm>
#include <vector>
#include <map>
#include <deque>
#include <iostream>
#include <fstream>
#include <pthread.h>
#include <unistd.h>
#include "parser.h"
#include "sat.h"

using namespace std;

sat::sat(vector<vector<int> > &clause_db, int maxVarIndex, int ori_db_size, int seed, int restart_chance, int numerator, int denominator):
  _clause_db(clause_db),
  _ori_db_size(ori_db_size),
  _cur_level(0),
  _seed(seed),
  _restart_chance(restart_chance),
  _max_var_idx(maxVarIndex),
  _numerator(numerator),
  _denominator(denominator),
  _learnt_size_limit(1),
  _n_conflict_to_restart(100),
  _n_conflict_to_restart_bound(100),
  _has_add_clause(false){

  /* init randomness hyper-parameters of simulated annealing */
  _init();
  _transfered_db_size = _clause_db.size();
}

void sat::get_learnt_clause(vector<vector<int> > &fill_learnt_clause){
  for(int c=_transfered_db_size; c<_clause_db.size(); ++c)
    fill_learnt_clause.push_back(_clause_db.at(c));
}

bool sat::solve(){
  if(!_preproc())
    return false;

  int n_conflict = 0;
  while(true){
    if(n_conflict >= _n_conflict_to_restart && _restart_chance > 0){
      _restart();
      _simulated_annealing();
      n_conflict = 0;
      --_restart_chance;
      if(!_preproc())
        return false;
    }
    vector<int> to_bcp_clause;
    to_bcp_clause.clear();
    int conflicting_clause, conflicting_var;
    if(!_branch_get_bcp_clause(to_bcp_clause)) // false means no unassigned var
      return true;

    while(!_bcp(to_bcp_clause, conflicting_clause, conflicting_var)){
      if(_cur_level == 0 && !_has_decision())
          return false;
      ++n_conflict;
      to_bcp_clause.clear();
      bool learnt = false;
      vector<int> learnt_clause;
      int back_level = _analyze_conflict(conflicting_clause, conflicting_var, learnt, learnt_clause);
      _backtrack(back_level, to_bcp_clause);
      if(learnt){
        int check_status = _check_learnt_clause(learnt_clause);
        if(check_status == NULL_CLAUSE)
          return false;
        if(check_status == COULD_ADD){
          _add_learnt_clause(learnt_clause);
          _has_add_clause = true;
          to_bcp_clause.push_back(_clause_db.size()-1);
        }
      }
    }
  }
}

int sat::thread_learn(int n_conflict_to_return, bool *time_to_ret){
  /* for thread invoking, similar to solve but break after n conflicts */
  if(!_preproc())
    return UNSAT;

  int n_conflict = 1;
  while(true){
    if(n_conflict % _n_conflict_to_restart == 0 && _restart_chance > 0){
      _restart();
      _simulated_annealing();
      --_restart_chance;
      if(!_preproc())
        return UNSAT;
    }
    vector<int> to_bcp_clause;
    to_bcp_clause.clear();
    int conflicting_clause, conflicting_var;
    if(!_branch_get_bcp_clause(to_bcp_clause)) // false means no unassigned var
      return SAT;

    while(!_bcp(to_bcp_clause, conflicting_clause, conflicting_var)){
      if(_cur_level == 0 && !_has_decision())
          return UNSAT;
      ++n_conflict;
      to_bcp_clause.clear();
      bool learnt = false;
      vector<int> learnt_clause;
      int back_level = _analyze_conflict(conflicting_clause, conflicting_var, learnt, learnt_clause);
      _backtrack(back_level, to_bcp_clause);
      if(learnt){
        int check_status = _check_learnt_clause(learnt_clause);
        if(check_status == NULL_CLAUSE)
          return UNSAT;
        if(check_status == COULD_ADD){
          _add_learnt_clause(learnt_clause);
          _has_add_clause = true;
          to_bcp_clause.push_back(_clause_db.size()-1);
        }
      }
      if(*time_to_ret)
        return NOT_YET;
    }
    if(n_conflict >= n_conflict_to_return || *time_to_ret){
      *time_to_ret = true;
      return NOT_YET;
    }
  }
}

void sat::write_result_file(char *filename){
  bool solved = _verify();
  int len = strlen(filename);
  filename[len-3] = 's'; filename[len-2] = 'a'; filename[len-1] = 't';
  ofstream fout(filename);
  if(solved){
      fout << "s SATISFIABLE\nv ";
      for(vector<var_info>::iterator vi = _var_info_vec.begin(); vi != _var_info_vec.end(); ++vi)
          fout << vi->value << ' ';
      fout << "0\n";
      cout << "SAT\n";
  }
  else{
      fout << "s UNSATISFIABLE\n";
      cout << "UNSAT\n";
  }
  fout.close();
}

bool sat::_verify(){
  for(int i=0; i<_ori_db_size; ++i){
    bool clause_check = false;
    for(vector<int>::iterator lit = _clause_db.at(i).begin(); lit != _clause_db.at(i).end(); ++lit){
        if(_var_info_vec.at(abs(*lit)).value == *lit){
            clause_check = true;
            break;
        }
    }
    if(!clause_check)
        return false;
  }
  return true;
}

void sat::_init(){
  _init_watch();
  _init_var_info();
  _init_to_assign_with_var_info();
  _assign_deque.clear();
  _cur_level = 0;
  _has_add_clause = false;
}

void sat::_init_var_info(){
  /* clear and init var_info_vec */
  _var_info_vec.clear();
  _var_info_vec.resize(_max_var_idx + 1); // [0] not used
  for(unsigned c=0; c<_clause_db.size(); ++c){
    for(vector<int>::iterator lit=_clause_db.at(c).begin(); lit!=_clause_db.at(c).end(); ++lit){
      int lit_idx = abs(*lit);
      if(*lit > 0)
        _var_info_vec.at(lit_idx).pos_vec.push_back(c);
      else
        _var_info_vec.at(lit_idx).neg_vec.push_back(c);
      _var_info_vec.at(lit_idx).score += 2;
    }
  }
}

void sat::_init_watch(){
  /* clear and init watch */
  _watch_db.clear();
  for(int c=0; c<_clause_db.size(); ++c){
    int size = _clause_db.at(c).size();
    if(size == 1)
      _watch_db.push_back(twoidx(0, 0));
    else{
      int idx1 = rand_r(&_seed) % size;
      int idx2 = rand_r(&_seed) % size;
      if(idx1 == idx2)
        idx2 = (idx1 + 1) % size;
      _watch_db.push_back(twoidx(idx1, idx2));
    }
  }
}

void sat::_init_to_assign_with_var_info(){
  /* clear and init to_assign_heap, to_assign_vec */
  _to_assign_heap.clear();
  _to_assign_vec.clear();
  for(int v=1; v<=_max_var_idx; ++v){
    _to_assign_heap.push_back(var_score(v, &_var_info_vec.at(v).score));
    _to_assign_vec.push_back(v);
  }
  make_heap(_to_assign_heap.begin(), _to_assign_heap.end(), _score_cmp);
}

void sat::_simulated_annealing(){
  if(_denominator < DENOMINATOR_HARD_LIMIT)
    _denominator += 1;
  if(_learnt_size_limit < LEARNT_SIZE_HARD_LIMIT && !_has_add_clause)
    _learnt_size_limit += 1;
  else if(_learnt_size_limit > 1)
    _learnt_size_limit -= 1;
  else
    ;
  if(_n_conflict_to_restart < _n_conflict_to_restart_bound)
    _n_conflict_to_restart *= 2;
  else{
    _n_conflict_to_restart = 100;
    if(_n_conflict_to_restart_bound < N_CONFLICT_TO_RESTART_HARD_LIMIT)
      _n_conflict_to_restart_bound *= 2;
  }
}

bool sat::_assign_handler(int var, int level, int antec, vector<int> &fill_bcp_clause){
  /* assign, update_watch, bcp */
  int assign_status = _try_assign(var, level, antec);
  if(assign_status == CONFLICT)
    return false;
  else if(assign_status == SUCCESSFULLY_ASSIGNED){
    vector<int>* to_check = var>0? &_var_info_vec.at(abs(var)).neg_vec: &_var_info_vec.at(abs(var)).pos_vec;
    _update_watch(*to_check);
    for(vector<int>::iterator it=to_check->begin(); it!=to_check->end(); ++it)
      fill_bcp_clause.push_back(*it);
    return true;
  }
  else
    return true;
}

int sat::_try_assign(int var, int level, int antec){
  /* check if no conflict then assign, else return false */
  int var_value = _var_info_vec.at(abs(var)).value;
  assert(var_value == var || var_value == UNASSIGNED || var_value == -var);
  if(var_value == var)
    return ALREADY_ASSIGNED_SAME;
  else if(var_value == UNASSIGNED){
    _assign(var, level, antec);
    return SUCCESSFULLY_ASSIGNED;
  }
  else
    return CONFLICT;
}

void sat::_assign(int var, int level, int antec){
  if(level == 0)
    _assign_deque.push_front(assignment(var, 0, antec));
  else
    _assign_deque.push_back(assignment(var, level, antec));
  int var_idx = abs(var);
  _var_info_vec.at(var_idx).value = var;
  _var_info_vec.at(var_idx).level = level;
  _var_info_vec.at(var_idx).antec = antec;
  _var_info_vec.at(var_idx).order = _assign_deque.size();
}

bool sat::_preproc(){
  vector<int> len_1_clause, one_phase_var, to_bcp_clause;
  _fill_len_1_clause(len_1_clause);
  for(vector<int>::iterator it=len_1_clause.begin(); it!=len_1_clause.end(); ++it){
    int var = _clause_db.at(*it).at(0);
    if(!_assign_handler(var, 0, *it, to_bcp_clause))
      return false;
  }
  _fill_1_phase_var(one_phase_var);
  for(vector<int>::iterator it=one_phase_var.begin(); it!=one_phase_var.end(); ++it){
    if(!_assign_handler(*it, 0, NO_ANTEC, to_bcp_clause))
      return false;
  }
  int conflicting_clause, conflicting_var;
  if(!_bcp(to_bcp_clause, conflicting_clause, conflicting_var))
    return false;
  return true;
}

void sat::_fill_len_1_clause(vector<int> &len_1_clause){
  for(int c=0; c<_clause_db.size(); ++c)
    if(_clause_db.at(c).size() == 1)
      len_1_clause.push_back(c);
}

void sat::_fill_1_phase_var(vector<int> &one_phase_var){
  for(int v=1; v<=_max_var_idx; ++v)
    if(_var_info_vec.at(v).neg_vec.size() == 0)
      one_phase_var.push_back(v);
    else if(_var_info_vec.at(v).pos_vec.size() == 0)
      one_phase_var.push_back(-v);
    else;
}

bool sat::_branch_get_bcp_clause(vector<int> &fill_bcp_clause){
  int to_assign_var;
  if(rand_r(&_seed) % _denominator < _numerator){ // random branch
    while(true){
      if(_to_assign_vec.empty())
        return false;
      int random_idx = rand_r(&_seed) % (_to_assign_vec.size());
      to_assign_var = _to_assign_vec.at(random_idx);
      _to_assign_vec.at(random_idx) = _to_assign_vec.back(); _to_assign_vec.pop_back();
      if(_var_info_vec.at(to_assign_var).value == UNASSIGNED)
        break;
    }
  }
  else{ // heuristic branch
    while(true){
      if(_to_assign_heap.empty())
        return false;
      to_assign_var = _to_assign_heap.front().var;
      pop_heap(_to_assign_heap.begin(), _to_assign_heap.end(), _score_cmp); _to_assign_heap.pop_back();
      if(_var_info_vec.at(to_assign_var).value == UNASSIGNED)
        break;
    }
  }
  if(rand_r(&_seed) % 2)
    to_assign_var *= -1;
  assert(_assign_handler(to_assign_var, ++_cur_level, NO_ANTEC, fill_bcp_clause) == true);
  return true;
}

void sat::_update_watch(vector<int> &clause_to_update){
  for(vector<int>::iterator it=clause_to_update.begin(); it!=clause_to_update.end(); ++it){
    if(_clause_db.at(*it).size() <= 2)
      continue;
    twoidx *watch = &_watch_db.at(*it);
    int var1 = _clause_db.at(*it).at(watch->idx1);
    int var2 = _clause_db.at(*it).at(watch->idx2);
    bool successfully_moved = true;
    if(var1 == -_var_info_vec.at(abs(var1)).value){
      successfully_moved = _try_move_watch(&watch->idx1, &watch->idx2, _clause_db.at(*it));
    }
    if(var2 == -_var_info_vec.at(abs(var2)).value && successfully_moved){
      _try_move_watch(&watch->idx2, &watch->idx1, _clause_db.at(*it));
    }
  }
}

bool sat::_try_move_watch(int *to_move, int *another, vector<int> &clause){
  int clause_size = clause.size();
  int ori_rand_loc = rand_r(&_seed) % clause_size;
  int rand_loc = (ori_rand_loc + 1) % clause_size;
  int var;
  while(true){
    var = clause.at(rand_loc);
    if(_var_info_vec.at(abs(var)).value != -var && rand_loc != *another || rand_loc == ori_rand_loc)
      break;
    else
      rand_loc = (rand_loc + 1) % clause_size;
  }
  *to_move = rand_loc;
  if(_var_info_vec.at(abs(var)).value != -var)
    return true;
  else
    return false;
}

bool sat::_bcp(vector<int> &to_bcp_clause, int &fill_c_clause, int &fill_c_var){
  /* if conflict, fill c_clause and c_var */
  for(int i=0; i<to_bcp_clause.size(); ++i){
    int clause_idx = to_bcp_clause.at(i);
    bool got_unit = false;
    int to_assign_var = 0;
    if(_clause_db.at(clause_idx).size() == 1){
      got_unit = true;
      to_assign_var = _clause_db.at(clause_idx).at(0);
    }
    else{
      int var1 = _clause_db.at(clause_idx).at(_watch_db.at(clause_idx).idx1);
      int var2 = _clause_db.at(clause_idx).at(_watch_db.at(clause_idx).idx2);
      if(_var_info_vec.at(abs(var1)).value == -var1){
        got_unit = true;
        to_assign_var = var2;
      }
      else if(_var_info_vec.at(abs(var2)).value == -var2){
        got_unit = true;
        to_assign_var = var1;
      }
      else;
    }
    if(got_unit){
      if(!_assign_handler(to_assign_var, _cur_level, clause_idx, to_bcp_clause)){
        fill_c_clause = clause_idx;
        fill_c_var = to_assign_var;
        return false;
      }
    }
  }
  return true;
}

bool sat::_has_decision(){
  for(deque<assignment>::iterator vit=_assign_deque.begin(); vit!=_assign_deque.end(); ++vit)
    if(vit->antec == NO_ANTEC)
      return true;
  return false;
}

int sat::_analyze_conflict(int c_clause_idx, int c_var, bool &learnt, vector<int> &fill_learnt_clause){
  vector<int> clause = _clause_db.at(c_clause_idx);
  _var_info_vec.at(abs(c_var)).order = _assign_deque.size()+1;
  _var_info_vec.at(abs(c_var)).level = _cur_level;
  learnt = _try_find_1uip(clause);
  if(learnt)
    fill_learnt_clause = clause;
  return _find_back_level(clause);
}

bool sat::_try_find_1uip(vector<int> &clause){
  bool find_something = false;
  int n_resolve = 0;
  int n_resolve_limit = _assign_deque.size();
  while(true){
    int most_recent_order = 0;
    int most_recent_assigned_var_idx = 0;
    int cur_level_implication_count = 0;
    for(vector<int>::iterator vit=clause.begin(); vit!=clause.end(); ++vit){
      int var_idx = abs(*vit);
      if(_var_info_vec.at(var_idx).level == _cur_level && _var_info_vec.at(var_idx).antec != NO_ANTEC){
        int order = _var_info_vec.at(var_idx).order;
        if(order > most_recent_order){
          most_recent_order = order;
          most_recent_assigned_var_idx = var_idx;
        }
        ++cur_level_implication_count;
      }
    }
    if(cur_level_implication_count < 2)
      break;
    _resolve(clause, _var_info_vec.at(most_recent_assigned_var_idx).antec, most_recent_assigned_var_idx);
    find_something = true;
    ++n_resolve;
    if(n_resolve >= n_resolve_limit)
      break;
  }
  return find_something;
}

void sat::_resolve(vector<int> &clause, int antec, int to_resolve_var_idx){
  bool pos_has[_max_var_idx + 1] = {false};
  bool neg_has[_max_var_idx + 1] = {false};
  for(vector<int>::iterator vit=clause.begin(); vit!=clause.end(); ++vit){
    if(*vit>0)
      pos_has[*vit] = true;
    else
      neg_has[-*vit] = true;
  }
  for(vector<int>::iterator vit=_clause_db.at(antec).begin(); vit!=_clause_db.at(antec).end(); ++vit){
    if(*vit>0)
      pos_has[*vit] = true;
    else
      neg_has[-*vit] = true;
  }
  clause.clear();
  for(int v=1; v<=_max_var_idx; ++v){
    if(pos_has[v] && v != to_resolve_var_idx)
      clause.push_back(v);
    if(neg_has[v] && v != to_resolve_var_idx)
      clause.push_back(-v);
  }
}

int sat::_find_back_level(vector<int> &clause){
  int back_level = 0;
  for(vector<int>::iterator vit=clause.begin(); vit!=clause.end(); ++vit){
    int level = _var_info_vec.at(abs(*vit)).level;
    if(level < _cur_level && level > back_level)
      back_level = level;
  }
  return back_level;
}

int sat::_check_learnt_clause(vector<int> &clause){
  if(clause.size() == 0)
    return NULL_CLAUSE;
  if(clause.size() > _learnt_size_limit){
    // add clasue evaluation policy here
    int false_count = 0;
    bool already_true = false;
    for(vector<int>::iterator vit=clause.begin(); vit!=clause.end(); ++vit){
      int var = _var_info_vec.at(abs(*vit)).value;
      if(var == *vit){
        already_true = true;
        break;
      }
      if(var == -*vit)
        ++false_count;
    }
    if(false_count == clause.size()-1)
      return COULD_ADD;
    if(already_true)
      return TOO_LARGE;
    //if(rand_r(&_seed) % (_denominator*clause.size()/2) < _numerator) // accept long clause...
    //  return COULD_ADD;
    return TOO_LARGE;
  }
  bool pos_has[_max_var_idx + 1] = {false};
  bool neg_has[_max_var_idx + 1] = {false};
  for(vector<int>::iterator vit=clause.begin(); vit!=clause.end(); ++vit){
    if(*vit>0){
      if(neg_has[*vit])
        return USELESS_CLAUSE;
      pos_has[*vit] = true;
    }
    else{
      if(pos_has[-*vit])
        return USELESS_CLAUSE;
      neg_has[-*vit] = true;
    }
  }
  return COULD_ADD;
}

void sat::_add_learnt_clause(vector<int> &clause){
  _clause_db.push_back(clause);

  for(vector<int>::iterator vit=clause.begin(); vit!=clause.end(); ++vit){
    if(*vit > 0)
      _var_info_vec.at(*vit).pos_vec.push_back(_clause_db.size()-1);
    else
      _var_info_vec.at(-*vit).neg_vec.push_back(_clause_db.size()-1);
    ++_var_info_vec.at(abs(*vit)).score;
  }

  if(clause.size() == 1)
    _watch_db.push_back(twoidx(0, 0));
  else{
    _watch_db.push_back(twoidx(0, 1));
    vector<int> clause_to_update(1, _watch_db.size()-1);
    _update_watch(clause_to_update);
  }
}

void sat::_backtrack(int back_level, vector<int> &fill_bcp_clause){
  for(int v=1; v<=_max_var_idx; ++v)
    --_var_info_vec.at(v).score;

  //if(rand_r(&_seed) % (_denominator*_cur_level) < _numerator)
   // back_level = rand_r(&_seed) % _cur_level;

  vector<int> to_update_watch;
  while(!_assign_deque.empty()){
    assignment as = _assign_deque.back();
    if(as.level > back_level || as.level == back_level && as.antec != NO_ANTEC || as.level == 0){
      _assign_deque.pop_back();
      int var_idx = abs(as.value);
      _var_info_vec.at(var_idx).value = UNASSIGNED;
      _to_assign_heap.push_back(var_score(var_idx, &_var_info_vec.at(var_idx).score));
      _to_assign_vec.push_back(var_idx);

      vector<int> *to_add_update;
      if(as.value > 0)
        to_add_update = &_var_info_vec.at(var_idx).neg_vec;
      else
        to_add_update = &_var_info_vec.at(var_idx).pos_vec;
      for(vector<int>::iterator cit=to_add_update->begin(); cit!=to_add_update->end(); ++cit)
        to_update_watch.push_back(*cit);
    }
    else 
      break;
  }
  _cur_level = back_level;
  _update_watch(to_update_watch);

  if(!_assign_deque.empty()){
    assignment as = _assign_deque.back();
    assert(as.antec == NO_ANTEC);
    if(as.value > 0)
      fill_bcp_clause = _var_info_vec.at(as.value).neg_vec;
    else
      fill_bcp_clause = _var_info_vec.at(-as.value).pos_vec;
  }

}

void sat::_restart(){
  _init();
}

void *mt_learn(void *arg_in){
  mt_arg *arg = (mt_arg *)arg_in;

  sat sat_solver(*(arg->clause_db), arg->max_var_idx, arg->ori_db_size, time(NULL)+pthread_self(), arg->restart_chance, arg->numerator, arg->denominator);
  mt_learn_ret *ret = new mt_learn_ret;
  ret->status = sat_solver.thread_learn(arg->n_conflict_to_return, &arg->time_to_ret);

  if(ret->status == SAT || ret->status == UNSAT){
    pthread_mutex_lock(arg->mutex);
    sat_solver.write_result_file(arg->result_file_name);

    clock_gettime(CLOCK_MONOTONIC, &sat_end_time);
    printf("\nthread %d finished. %f sec\n", pthread_self(), diff_time_sec(&sat_start_time, &sat_end_time));
    exit(0);
  }
  else
    sat_solver.get_learnt_clause(ret->learnt_clause);

  return (void *)ret;
}

void *mt_solve(void *arg_in){
  mt_arg *arg = (mt_arg *)arg_in;

  sat sat_solver(*(arg->clause_db), arg->max_var_idx, arg->ori_db_size, time(NULL)+pthread_self(), arg->restart_chance, arg->numerator, arg->denominator);
  sat_solver.solve();

  pthread_mutex_lock(arg->mutex);
  sat_solver.write_result_file(arg->result_file_name);

  clock_gettime(CLOCK_MONOTONIC, &sat_end_time);
  printf("\nthread solve finished. %f sec\n", diff_time_sec(&sat_start_time, &sat_end_time));
  exit(0);

  return (void *)NULL;
}

double diff_time_sec(struct timespec *start, struct timespec *end){
  double diff = end->tv_sec - start->tv_sec + double(end->tv_nsec - start->tv_nsec) / 1e9;
  return diff;
}

int main(int argc, char *argv[]){
  if(argc != 2){
    cout << "Usage: ./yasat cnf_file_path\n";
    exit(1);
  }
  clock_gettime(CLOCK_MONOTONIC, &sat_start_time);

  vector<vector<int> > clause_db;
  int maxVarIndex;
  parse_DIMACS_CNF(clause_db, maxVarIndex, argv[1]);
  int ori_db_size = clause_db.size();

  //int n_thread = sysconf(_SC_NPROCESSORS_ONLN);
  int n_thread = 16;
  int restart_chance = 1e6; // decay
  int numerator = 128; // decay 
  int denominator = 256; // decay
  int n_conflict_to_return = 64; // increasing
  int n_conflict_to_return_bound = 128; // increasing
  int n_timestep_to_change = 5;
  pthread_mutex_t mutex;
  pthread_t tid[n_thread];
  mt_arg arg(&clause_db, maxVarIndex, ori_db_size, 10000, 256, 512, 0, argv[1], &mutex);

  /* thread solve */
  pthread_create(&tid[0], NULL, &mt_solve, (void *)&arg);

  /* thread mt_learn */
  map<vector<int>, bool> hash_map;
  for(vector<vector<int> >::iterator cit=clause_db.begin(); cit!=clause_db.end(); ++cit){
    hash_map[*cit] = true;
  }

  printf("\n");
  for(int timestep=1; timestep<65536; ++timestep){
    arg.clause_db = &clause_db;
    arg.restart_chance = restart_chance;
    arg.numerator = numerator;
    arg.denominator = denominator;
    arg.n_conflict_to_return = n_conflict_to_return;
    arg.time_to_ret = false;
    for(int i=1; i<n_thread; ++i){
      pthread_create(&tid[i], NULL, &mt_learn, (void *)&arg);
    }

    mt_learn_ret *ret[n_thread];
    for(int i=1; i<n_thread; ++i){
      pthread_join(tid[i], (void**)&ret[i]);
    }

    int count = 0;
    for(int i=1; i<n_thread; ++i){
      for(vector<vector<int> >::iterator cit=ret[i]->learnt_clause.begin(); cit!=ret[i]->learnt_clause.end(); ++cit){
        if(hash_map.find(*cit) == hash_map.end()){
          hash_map[*cit] = true;
          clause_db.push_back(*cit);
          ++count;
        }
        clause_db.push_back(*cit);
      }
      delete ret[i];
      printf("\r[%d/65535] %d clauses added. clause_db_size = %lu..... ", timestep, count, clause_db.size());
    }
  
    if(timestep % n_timestep_to_change == 0){
      if(restart_chance > 100)
        restart_chance -= 100;
      if(numerator != 1){
        numerator /= 2;
        denominator /= 2;
      }
      if(n_conflict_to_return < n_conflict_to_return_bound)
        n_conflict_to_return *= 2;
      else{
        n_conflict_to_return = 64;
        if(n_conflict_to_return_bound < 65535)
          n_conflict_to_return_bound *= 2;
      }
    }

    clock_gettime(CLOCK_MONOTONIC, &sat_cur_time);
    if(diff_time_sec(&sat_start_time, &sat_cur_time) > 900){
      printf("break due to timelimit...\n");
      break;
    }
  }
  return 0;
}
