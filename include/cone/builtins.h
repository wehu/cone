       
#pragma once

#include <pybind11/pybind11.h>
#include <pybind11/functional.h>

namespace cone {

  namespace py = pybind11;

  typedef py::object object;

  typedef std::function<object(object)> cont;

  typedef object states;

  typedef object effects;

  inline object cone__print(const cont &k, states s, effects effs, const object &a) {
    py::print(a);
    return k(a);
  }

  inline object ____lookup_var(states s, const std::string &key) {
    auto l = py::cast<py::list>(s);
    for (auto it=l.begin(); it != l.end(); ++it) {
      auto m = py::cast<py::dict>(*it);
      if (m.contains(key)) {
        return py::getattr(m, key.c_str());
      }
    }
    return py::none();
  }

  inline object ____lookup_eff(effects effs, const std::string &key) {
    auto l = py::cast<py::list>(effs);
    for (auto it=l.begin(); it != l.end(); ++it) {
      auto m = py::cast<py::dict>(*it);
      if (m.contains(key)) {
        return py::getattr(m, key.c_str());
      }
    }
    return py::none();
  }

  inline object ____add_var(states s, const std::string &key, const object &k) {
    auto l = py::cast<py::list>(s);
    py::setattr(l[0], key.c_str(), k);
    return py::none();
  }

  inline object ____update_state(states s, const std::string &key, const object &k) {
    auto l = py::cast<py::list>(s);
    for (auto it=l.begin(); it != l.end(); ++it) {
      auto m = py::cast<py::dict>(*it);
      if (m.contains(key)) {
        setattr(m, key.c_str(), k);
        return py::none();
      }
    }
    return py::none();
  }

  inline object ____call_cps_with_cleared_vars(
    const cont &k, states s, effects es,
    const std::vector<std::string> &ks, object e) {
    auto state = s;
    effects effs;
    auto l = py::cast<py::list>(state);
    for (auto it=l.begin(); it!=l.end(); ++it) {
      for (auto k : ks) {
        py::delattr(*it, k.c_str());
      }
    }
    return e(k, state, effs);
  }

  inline object ____while(const cont &k, states state, effects effs,
                          const object &cond,
                          const object &body) {
    auto l = py::cast<py::list>(state);
    l.insert(0, py::dict());
    cont k2;
    std::shared_ptr<cont> k3;
    k2 = [state, effs, k, k3, body](const object &o) {
      auto l = py::cast<py::list>(state);
      if (py::cast<bool>(o)) {
        l.insert(0, py::dict());
        return body(*k3, state, effs);
      } else {
        return k(o);
      }
    };
    k3 = std::make_shared<cont>([state, effs, k2, cond](const object &o) {
      auto l = py::cast<py::list>(state);
      l.attr("pop")(0);
      return cond(k2, state, effs);
    });
    return cond(k2, state, effs);
  }

  inline object ____case(const cont &k, states state, effects effs, const object &ce,
                         const std::vector<std::function<bool(object)>> &conds,
                         const std::vector<object> &exprs) {
    for (unsigned i=0; i<conds.size(); ++i) {
      const auto &p = conds[i];
      const auto &e = exprs[i];
      auto l = py::cast<py::list>(state);
      l.insert(0, py::dict());
      const cont k2 = [state, k](const object &o) {
        auto l = py::cast<py::list>(state);
        l.attr("pop")(0);
        return k(o);
      };
      if (p(ce)) {
        return e(k2, state, effs);
      } else {
        l.attr("pop")(0);
      }
    }
  }

  const cont identity_k = [](const object &x) { return x; };

  inline object ____handle(const cont &k, states state, effects effs,
                          const object &scope, const object &handlers) {
    auto sl = py::cast<py::list>(state);
    auto el = py::cast<py::list>(effs);
    sl.insert(0, py::dict());
    el.insert(0, py::dict());
    el[0].attr("update")(handlers);
    auto &&o = scope(identity_k, state, effs);
    sl.attr("pop")(0);
    el.attr("pop")(0);
    return k(o);
  }

  constexpr auto ____resumed_k = "____resumed_k";

  inline object ____call_with_resumed_k(const cont &k, states state, effects effs, const object &handler) {
    auto l = py::cast<py::list>(state);
    l.insert(0, py::dict());
    py::setattr(l[0], ____resumed_k, py::cpp_function(k));
    auto &&o = handler(identity_k, state, effs);
    l.attr("pop")(0);
    return o;
  }

  inline object cone__resume(const cont &k, states s, effects effs, const object &a) {
    auto l = py::cast<py::list>(s);
    return k(py::getattr(l[0], ____resumed_k)(a));
  }

}