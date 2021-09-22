       
#pragma once

#include <pybind11.h>
#include <pybind11/functional.h>
#include <iostream>
#include <map>
#include <vector>
#include <functional>
#include <memory>
#include <string>

namespace cone {

  namespace py = pybind11;

  typedef py::object object;

  typedef std::function<py::object(py::object)> cont;

  typedef py::object states;

  typedef py::object effects;

  inline object cone_print(const cont &k, states s, effects effs, const object &a) {
    py::print(a);
    return k(a);
  }

  inline object ____lookup_var(states s, const std::string &key) {
    for (auto it=s.rbegin(); it != s.rend(); ++it) {
      if (it->find(key) != it->end()) {
        return (*it)[key];
      }
    }
    return py::none;
  }

  inline object ____lookup_eff(effects effs, const std::string &key) {
    for (auto it=effs.rbegin(); it != effs.rend(); ++it) {
      if (it->find(key) != it->end()) {
        return (*it)[key];
      }
    }
    return unit;
  }

  inline object ____add_var(states s, const std::string &key, const object &k) {
    s[s.size()-1][key] = k;
    return unit;
  }

  inline object ____update_state(states s, const std::string &key, const object &k) {
    for (auto it=s.rbegin(); it != s.rend(); ++it) {
      if (it->find(key) != it->end()) {
        (*it)[key] = k;
        return unit;
      }
    }
    return unit;
  }

  inline object ____call_cps_with_cleared_vars(
    const cont &k, states &&s, effects &&es,
    const std::vector<std::string> &ks, object e) {
    auto state = s;
    effects effs;
    for (auto it=s.begin(); it!=s.end(); ++it) {
      for (auto k : ks) {
        it->erase(k);
      }
    }
    return std::any_cast<cont_with_state>(e)(k, std::move(state), std::move(effs));
  }

  inline object ____while(const cont &k, states &&state, effects &&effs,
                          const object &cond,
                          const object &body) {
    state.push_back({});
    cont k2;
    std::shared_ptr<cont> k3;
    k2 = [&state, &effs, k, k3, body](const object &o) {
      if (std::any_cast<bool>(o)) {
        state.push_back({});
        return std::any_cast<cont_with_state>(body)(*k3, std::move(state), std::move(effs));
      } else {
        return k(o);
      }
    };
    k3 = std::make_shared<cont>([&state, &effs, k2, cond](const object &o) {
      state.pop_back();
      return std::any_cast<cont_with_state>(cond)(k2, std::move(state), std::move(effs));
    });
    return std::any_cast<cont_with_state>(cond)(k2, std::move(state), std::move(effs));
  }

  inline object ____case(const cont &k, states &&state, effects &&effs, const object &ce,
                         const std::vector<std::function<bool(object)>> &conds,
                         const std::vector<object> &exprs) {
    for (unsigned i=0; i<conds.size(); ++i) {
      const auto &p = conds[i];
      const auto &e = exprs[i];
      state.push_back({});
      const cont k2 = [&state, k](const object &o) {
        state.pop_back();
        return k(o);
      };
      if (p(ce)) {
        return std::any_cast<cont_with_state>(e)(k2, std::move(state), std::move(effs));
      }
      state.pop_back();
    }
  }

  const cont identity_k = [](const object &x) { return x; };

  inline object ____handle(const cont &k, states &&state, effects &&effs,
                          const object &scope, std::map<std::string, object> &handlers) {
    state.push_back({});
    effs.push_back({});
    effs[effs.size()-1].merge(handlers);
    auto &&o = k(std::any_cast<cont_with_state>(scope)(identity_k, std::move(state), std::move(effs)));
    state.pop_back();
    effs.pop_back();
    return o;
  }

  constexpr auto ____resumed_k = "____resumed_k";

  inline object ____call_with_resumed_k(const cont &k, states &&state, effects &&effs, const object &handler) {
    state.push_back({});
    state[state.size()-1][____resumed_k] = k;
    auto &&o = std::any_cast<cont_with_state>(handler)(identity_k, std::move(state), std::move(effs));
    state.pop_back();
    return o;
  }

  inline object cone_resume(const cont &k, states &&s, effects &&effs, const object &a) {
    return k(std::any_cast<cont>(s[s.size()-1][____resumed_k])(a));
  }

}