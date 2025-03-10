// https://github.com/rust-lang/rust/blob/master/src/librustdoc/html/static/js/search.js
// eslint-disable-next-line no-unused-vars
function hasOwnPropertyRustdoc(obj, property) {
  return Object.prototype.hasOwnProperty.call(obj, property);
}
function onEach(arr, func, reversed) {
  if (arr && arr.length > 0 && func) {
    var length = arr.length;
    var i;
    if (reversed) {
      for (i = length - 1; i >= 0; --i) {
        if (func(arr[i])) {
          return true;
        }
      }
    } else {
      for (i = 0; i < length; ++i) {
        if (func(arr[i])) {
          return true;
        }
      }
    }
  }
  return false;
}

function removeEmptyStringsFromArray(x) {
  for (var i = 0, len = x.length; i < len; ++i) {
    if (x[i] === "") {
      x.splice(i, 1);
      i -= 1;
    }
  }
}

// This mapping table should match the discriminants of
// `rustdoc::html::item_type::ItemType` type in Rust.
exports.itemTypes = itemTypes = [
  "mod",
  "externcrate",
  "import",
  "struct",
  "enum",
  "fn",
  "type",
  "static",
  "trait",
  "impl",
  "tymethod",
  "method",
  "structfield",
  "variant",
  "macro",
  "primitive",
  "associatedtype",
  "constant",
  "associatedconstant",
  "union",
  "foreigntype",
  "keyword",
  "existential",
  "attr",
  "derive",
  "traitalias",
];

// used for special search precedence
var TY_PRIMITIVE = itemTypes.indexOf("primitive");
var TY_KEYWORD = itemTypes.indexOf("keyword");

/**
 * A function to compute the Levenshtein distance between two strings
 * Licensed under the Creative Commons Attribution-ShareAlike 3.0 Unported
 * Full License can be found at http://creativecommons.org/licenses/by-sa/3.0/legalcode
 * This code is an unmodified version of the code written by Marco de Wit
 * and was found at http://stackoverflow.com/a/18514751/745719
 */
var levenshtein_row2 = [];

function levenshtein(s1, s2) {
  if (s1 === s2) {
    return 0;
  }
  var s1_len = s1.length,
    s2_len = s2.length;
  if (s1_len && s2_len) {
    var i1 = 0,
      i2 = 0,
      a,
      b,
      c,
      c2,
      row = levenshtein_row2;
    while (i1 < s1_len) {
      row[i1] = ++i1;
    }
    while (i2 < s2_len) {
      c2 = s2.charCodeAt(i2);
      a = i2;
      ++i2;
      b = i2;
      for (i1 = 0; i1 < s1_len; ++i1) {
        c = a + (s1.charCodeAt(i1) !== c2 ? 1 : 0);
        a = row[i1];
        b = b < a ? (b < c ? b + 1 : c) : a < c ? a + 1 : c;
        row[i1] = b;
      }
    }
    return b;
  }
  return s1_len + s2_len;
}

const window = {
  rootPath: "./",
};
const rootPath = './';

function initSearch(rawSearchIndex) {
  var MAX_LEV_DISTANCE = 3;
  var MAX_RESULTS = 200;
  var GENERICS_DATA = 2;
  var NAME = 0;
  var INPUTS_DATA = 0;
  var OUTPUT_DATA = 1;
  var NO_TYPE_FILTER = -1;
  var currentResults, index, searchIndex;
  var ALIASES = {};

  /**
   * Executes the query and builds an index of results
   * @param  {[Object]} query      [The user query]
   * @param  {[type]} searchWords  [The list of search words to query
   *                                against]
   * @param  {[type]} filterCrates [Crate to search in if defined]
   * @return {[type]}              [A search index of results]
   */
  function execQuery(query, searchWords, filterCrates) {
    function itemTypeFromName(typename) {
      for (var i = 0, len = itemTypes.length; i < len; ++i) {
        if (itemTypes[i] === typename) {
          return i;
        }
      }
      return NO_TYPE_FILTER;
    }

    var valLower = query.query.toLowerCase(),
      val = valLower,
      typeFilter = itemTypeFromName(query.type),
      results = {},
      results_in_args = {},
      results_returned = {},
      split = valLower.split("::");

    removeEmptyStringsFromArray(split);

    function transformResults(results) {
      var out = [];
      for (var i = 0, len = results.length; i < len; ++i) {
        if (results[i].id > -1) {
          var obj = searchIndex[results[i].id];
          obj.lev = results[i].lev;
          var res = buildHrefAndPath(obj);
          obj.displayPath = pathSplitter(res[0]);
          obj.fullPath = obj.displayPath + obj.name;
          // To be sure than it some items aren't considered as duplicate.
          obj.fullPath += "|" + obj.ty;
          obj.href = res[1];
          out.push(obj);
          if (out.length >= MAX_RESULTS) {
            break;
          }
        }
      }
      return out;
    }

    function sortResults(results, isType) {
      var ar = [];
      for (var entry in results) {
        if (hasOwnPropertyRustdoc(results, entry)) {
          ar.push(results[entry]);
        }
      }
      results = ar;
      var i, len, result;
      for (i = 0, len = results.length; i < len; ++i) {
        result = results[i];
        result.word = searchWords[result.id];
        result.item = searchIndex[result.id] || {};
      }
      // if there are no results then return to default and fail
      if (results.length === 0) {
        return [];
      }

      results.sort(function (aaa, bbb) {
        var a, b;

        // sort by exact match with regard to the last word (mismatch goes later)
        a = aaa.word !== val;
        b = bbb.word !== val;
        if (a !== b) {
          return a - b;
        }

        // Sort by non levenshtein results and then levenshtein results by the distance
        // (less changes required to match means higher rankings)
        a = aaa.lev;
        b = bbb.lev;
        if (a !== b) {
          return a - b;
        }

        // sort by crate (non-current crate goes later)
        a = aaa.item.crate !== window.currentCrate;
        b = bbb.item.crate !== window.currentCrate;
        if (a !== b) {
          return a - b;
        }

        // sort by item name length (longer goes later)
        a = aaa.word.length;
        b = bbb.word.length;
        if (a !== b) {
          return a - b;
        }

        // sort by item name (lexicographically larger goes later)
        a = aaa.word;
        b = bbb.word;
        if (a !== b) {
          return a > b ? +1 : -1;
        }

        // sort by index of keyword in item name (no literal occurrence goes later)
        a = aaa.index < 0;
        b = bbb.index < 0;
        if (a !== b) {
          return a - b;
        }
        // (later literal occurrence, if any, goes later)
        a = aaa.index;
        b = bbb.index;
        if (a !== b) {
          return a - b;
        }

        // special precedence for primitive and keyword pages
        if (
          (aaa.item.ty === TY_PRIMITIVE && bbb.item.ty !== TY_KEYWORD) ||
          (aaa.item.ty === TY_KEYWORD && bbb.item.ty !== TY_PRIMITIVE)
        ) {
          return -1;
        }
        if (
          (bbb.item.ty === TY_PRIMITIVE && aaa.item.ty !== TY_PRIMITIVE) ||
          (bbb.item.ty === TY_KEYWORD && aaa.item.ty !== TY_KEYWORD)
        ) {
          return 1;
        }

        // sort by description (no description goes later)
        a = aaa.item.desc === "";
        b = bbb.item.desc === "";
        if (a !== b) {
          return a - b;
        }

        // sort by type (later occurrence in `itemTypes` goes later)
        a = aaa.item.ty;
        b = bbb.item.ty;
        if (a !== b) {
          return a - b;
        }

        // sort by path (lexicographically larger goes later)
        a = aaa.item.path;
        b = bbb.item.path;
        if (a !== b) {
          return a > b ? +1 : -1;
        }

        // que sera, sera
        return 0;
      });

      for (i = 0, len = results.length; i < len; ++i) {
        result = results[i];

        // this validation does not make sense when searching by types
        if (result.dontValidate) {
          continue;
        }
        var name = result.item.name.toLowerCase(),
          path = result.item.path.toLowerCase(),
          parent = result.item.parent;

        if (!isType && !validateResult(name, path, split, parent)) {
          result.id = -1;
        }
      }
      return transformResults(results);
    }

    function extractGenerics(val) {
      val = val.toLowerCase();
      if (val.indexOf("<") !== -1) {
        var values = val.substring(val.indexOf("<") + 1, val.lastIndexOf(">"));
        return {
          name: val.substring(0, val.indexOf("<")),
          generics: values.split(/\s*,\s*/),
        };
      }
      return {
        name: val,
        generics: [],
      };
    }

    function checkGenerics(obj, val) {
      // The names match, but we need to be sure that all generics kinda
      // match as well.
      var tmp_lev, elem_name;
      if (val.generics.length > 0) {
        if (
          obj.length > GENERICS_DATA &&
          obj[GENERICS_DATA].length >= val.generics.length
        ) {
          var elems = Object.create(null);
          var elength = obj[GENERICS_DATA].length;
          for (var x = 0; x < elength; ++x) {
            if (!elems[obj[GENERICS_DATA][x][NAME]]) {
              elems[obj[GENERICS_DATA][x][NAME]] = 0;
            }
            elems[obj[GENERICS_DATA][x][NAME]] += 1;
          }
          var total = 0;
          var done = 0;
          // We need to find the type that matches the most to remove it in order
          // to move forward.
          var vlength = val.generics.length;
          for (x = 0; x < vlength; ++x) {
            var lev = MAX_LEV_DISTANCE + 1;
            var firstGeneric = val.generics[x];
            var match = null;
            if (elems[firstGeneric]) {
              match = firstGeneric;
              lev = 0;
            } else {
              for (elem_name in elems) {
                tmp_lev = levenshtein(elem_name, firstGeneric);
                if (tmp_lev < lev) {
                  lev = tmp_lev;
                  match = elem_name;
                }
              }
            }
            if (match !== null) {
              elems[match] -= 1;
              if (elems[match] == 0) {
                delete elems[match];
              }
              total += lev;
              done += 1;
            } else {
              return MAX_LEV_DISTANCE + 1;
            }
          }
          return Math.ceil(total / done);
        }
      }
      return MAX_LEV_DISTANCE + 1;
    }

    // Check for type name and type generics (if any).
    function checkType(obj, val, literalSearch) {
      var lev_distance = MAX_LEV_DISTANCE + 1;
      var tmp_lev = MAX_LEV_DISTANCE + 1;
      var len, x, firstGeneric;
      if (obj[NAME] === val.name) {
        if (literalSearch) {
          if (val.generics && val.generics.length !== 0) {
            if (obj.length > GENERICS_DATA && obj[GENERICS_DATA].length > 0) {
              var elems = Object.create(null);
              len = obj[GENERICS_DATA].length;
              for (x = 0; x < len; ++x) {
                if (!elems[obj[GENERICS_DATA][x][NAME]]) {
                  elems[obj[GENERICS_DATA][x][NAME]] = 0;
                }
                elems[obj[GENERICS_DATA][x][NAME]] += 1;
              }

              var allFound = true;
              len = val.generics.length;
              for (x = 0; x < len; ++x) {
                firstGeneric = val.generics[x];
                if (elems[firstGeneric]) {
                  elems[firstGeneric] -= 1;
                } else {
                  allFound = false;
                  break;
                }
              }
              if (allFound) {
                return true;
              }
            }
            return false;
          }
          return true;
        } else {
          // If the type has generics but don't match, then it won't return at this point.
          // Otherwise, `checkGenerics` will return 0 and it'll return.
          if (obj.length > GENERICS_DATA && obj[GENERICS_DATA].length !== 0) {
            tmp_lev = checkGenerics(obj, val);
            if (tmp_lev <= MAX_LEV_DISTANCE) {
              return tmp_lev;
            }
          }
        }
      } else if (literalSearch) {
        if (
          (!val.generics || val.generics.length === 0) &&
          obj.length > GENERICS_DATA &&
          obj[GENERICS_DATA].length > 0
        ) {
          return obj[GENERICS_DATA].some(function (gen) {
            return gen[NAME] === val.name;
          });
        }
        return false;
      }
      lev_distance = Math.min(levenshtein(obj[NAME], val.name), lev_distance);
      if (lev_distance <= MAX_LEV_DISTANCE) {
        // The generics didn't match but the name kinda did so we give it
        // a levenshtein distance value that isn't *this* good so it goes
        // into the search results but not too high.
        lev_distance = Math.ceil((checkGenerics(obj, val) + lev_distance) / 2);
      }
      if (obj.length > GENERICS_DATA && obj[GENERICS_DATA].length > 0) {
        // We can check if the type we're looking for is inside the generics!
        var olength = obj[GENERICS_DATA].length;
        for (x = 0; x < olength; ++x) {
          tmp_lev = Math.min(
            levenshtein(obj[GENERICS_DATA][x][NAME], val.name),
            tmp_lev
          );
        }
        if (tmp_lev !== 0) {
          // If we didn't find a good enough result, we go check inside the generics of
          // the generics.
          for (x = 0; x < olength && tmp_lev !== 0; ++x) {
            tmp_lev = Math.min(
              checkType(obj[GENERICS_DATA][x], val, literalSearch),
              tmp_lev
            );
          }
        }
      }
      // Now whatever happens, the returned distance is "less good" so we should mark it
      // as such, and so we add 1 to the distance to make it "less good".
      return Math.min(lev_distance, tmp_lev) + 1;
    }

    function findArg(obj, val, literalSearch, typeFilter) {
      var lev_distance = MAX_LEV_DISTANCE + 1;

      if (
        obj &&
        obj.type &&
        obj.type[INPUTS_DATA] &&
        obj.type[INPUTS_DATA].length > 0
      ) {
        var length = obj.type[INPUTS_DATA].length;
        for (var i = 0; i < length; i++) {
          var tmp = obj.type[INPUTS_DATA][i];
          if (!typePassesFilter(typeFilter, tmp[1])) {
            continue;
          }
          tmp = checkType(tmp, val, literalSearch);
          if (literalSearch) {
            if (tmp) {
              return true;
            }
            continue;
          }
          lev_distance = Math.min(tmp, lev_distance);
          if (lev_distance === 0) {
            return 0;
          }
        }
      }
      return literalSearch ? false : lev_distance;
    }

    function checkReturned(obj, val, literalSearch, typeFilter) {
      var lev_distance = MAX_LEV_DISTANCE + 1;

      if (obj && obj.type && obj.type.length > OUTPUT_DATA) {
        var ret = obj.type[OUTPUT_DATA];
        if (typeof ret[0] === "string") {
          ret = [ret];
        }
        for (var x = 0, len = ret.length; x < len; ++x) {
          var tmp = ret[x];
          if (!typePassesFilter(typeFilter, tmp[1])) {
            continue;
          }
          tmp = checkType(tmp, val, literalSearch);
          if (literalSearch) {
            if (tmp) {
              return true;
            }
            continue;
          }
          lev_distance = Math.min(tmp, lev_distance);
          if (lev_distance === 0) {
            return 0;
          }
        }
      }
      return literalSearch ? false : lev_distance;
    }

    function checkPath(contains, lastElem, ty) {
      if (contains.length === 0) {
        return 0;
      }
      var ret_lev = MAX_LEV_DISTANCE + 1;
      var path = ty.path.split("::");

      if (ty.parent && ty.parent.name) {
        path.push(ty.parent.name.toLowerCase());
      }

      var length = path.length;
      var clength = contains.length;
      if (clength > length) {
        return MAX_LEV_DISTANCE + 1;
      }
      for (var i = 0; i < length; ++i) {
        if (i + clength > length) {
          break;
        }
        var lev_total = 0;
        var aborted = false;
        for (var x = 0; x < clength; ++x) {
          var lev = levenshtein(path[i + x], contains[x]);
          if (lev > MAX_LEV_DISTANCE) {
            aborted = true;
            break;
          }
          lev_total += lev;
        }
        if (!aborted) {
          ret_lev = Math.min(ret_lev, Math.round(lev_total / clength));
        }
      }
      return ret_lev;
    }

    function typePassesFilter(filter, type) {
      // No filter
      if (filter <= NO_TYPE_FILTER) return true;

      // Exact match
      if (filter === type) return true;

      // Match related items
      var name = itemTypes[type];
      switch (itemTypes[filter]) {
        case "constant":
          return name === "associatedconstant";
        case "fn":
          return name === "method" || name === "tymethod";
        case "type":
          return name === "primitive" || name === "associatedtype";
        case "trait":
          return name === "traitalias";
      }

      // No match
      return false;
    }

    function createAliasFromItem(item) {
      return {
        crate: item.crate,
        name: item.name,
        path: item.path,
        desc: item.desc,
        ty: item.ty,
        parent: item.parent,
        type: item.type,
        is_alias: true,
        
      };
    }

    function handleAliases(ret, query, filterCrates) {
      // We separate aliases and crate aliases because we want to have current crate
      // aliases to be before the others in the displayed results.
      var aliases = [];
      var crateAliases = [];
      if (filterCrates !== undefined) {
        if (ALIASES[filterCrates] && ALIASES[filterCrates][query.search]) {
          var query_aliases = ALIASES[filterCrates][query.search];
          var len = query_aliases.length;
          for (var i = 0; i < len; ++i) {
            aliases.push(createAliasFromItem(searchIndex[query_aliases[i]]));
          }
        }
      } else {
        Object.keys(ALIASES).forEach(function (crate) {
          if (ALIASES[crate][query.search]) {
            var pushTo = crate === window.currentCrate ? crateAliases : aliases;
            var query_aliases = ALIASES[crate][query.search];
            var len = query_aliases.length;
            for (var i = 0; i < len; ++i) {
              pushTo.push(createAliasFromItem(searchIndex[query_aliases[i]]));
            }
          }
        });
      }

      var sortFunc = function (aaa, bbb) {
        if (aaa.path < bbb.path) {
          return 1;
        } else if (aaa.path === bbb.path) {
          return 0;
        }
        return -1;
      };
      crateAliases.sort(sortFunc);
      aliases.sort(sortFunc);

      var pushFunc = function (alias) {
        alias.alias = query.raw;
        var res = buildHrefAndPath(alias);
        alias.displayPath = pathSplitter(res[0]);
        alias.fullPath = alias.displayPath + alias.name;
        alias.href = res[1];

        ret.others.unshift(alias);
        if (ret.others.length > MAX_RESULTS) {
          ret.others.pop();
        }
      };
      onEach(aliases, pushFunc);
      onEach(crateAliases, pushFunc);
    }

    // quoted values mean literal search
    var nSearchWords = searchWords.length;
    var i, it;
    var ty;
    var fullId;
    var returned;
    var in_args;
    var len;
    if (
      (val.charAt(0) === '"' || val.charAt(0) === "'") &&
      val.charAt(val.length - 1) === val.charAt(0)
    ) {
      val = extractGenerics(val.substr(1, val.length - 2));
      for (i = 0; i < nSearchWords; ++i) {
        if (
          filterCrates !== undefined &&
          searchIndex[i].crate !== filterCrates
        ) {
          continue;
        }
        in_args = findArg(searchIndex[i], val, true, typeFilter);
        returned = checkReturned(searchIndex[i], val, true, typeFilter);
        ty = searchIndex[i];
        fullId = ty.id;

        if (
          searchWords[i] === val.name &&
          typePassesFilter(typeFilter, searchIndex[i].ty) &&
          results[fullId] === undefined
        ) {
          results[fullId] = {
            id: i,
            index: -1,
            dontValidate: true,
          };
        }
        if (in_args && results_in_args[fullId] === undefined) {
          results_in_args[fullId] = {
            id: i,
            index: -1,
            dontValidate: true,
          };
        }
        if (returned && results_returned[fullId] === undefined) {
          results_returned[fullId] = {
            id: i,
            index: -1,
            dontValidate: true,
          };
        }
      }
      query.inputs = [val];
      query.output = val;
      query.search = val;
      // searching by type
    } else if (val.search("->") > -1) {
      var trimmer = function (s) {
        return s.trim();
      };
      var parts = val.split("->").map(trimmer);
      var input = parts[0];
      // sort inputs so that order does not matter
      var inputs = input.split(",").map(trimmer).sort();
      for (i = 0, len = inputs.length; i < len; ++i) {
        inputs[i] = extractGenerics(inputs[i]);
      }
      var output = extractGenerics(parts[1]);

      for (i = 0; i < nSearchWords; ++i) {
        if (
          filterCrates !== undefined &&
          searchIndex[i].crate !== filterCrates
        ) {
          continue;
        }
        var type = searchIndex[i].type;
        ty = searchIndex[i];
        if (!type) {
          continue;
        }
        fullId = ty.id;

        returned = checkReturned(ty, output, true, NO_TYPE_FILTER);
        if (output.name === "*" || returned) {
          in_args = false;
          var is_module = false;

          if (input === "*") {
            is_module = true;
          } else {
            var allFound = true;
            for (it = 0, len = inputs.length; allFound && it < len; it++) {
              allFound = checkType(type, inputs[it], true);
            }
            in_args = allFound;
          }
          if (in_args) {
            results_in_args[fullId] = {
              id: i,
              index: -1,
              dontValidate: true,
            };
          }
          if (returned) {
            results_returned[fullId] = {
              id: i,
              index: -1,
              dontValidate: true,
            };
          }
          if (is_module) {
            results[fullId] = {
              id: i,
              index: -1,
              dontValidate: true,
            };
          }
        }
      }
      query.inputs = inputs.map(function (input) {
        return input.name;
      });
      query.output = output.name;
    } else {
      query.inputs = [val];
      query.output = val;
      query.search = val;
      // gather matching search results up to a certain maximum
      val = val.replace(/_/g, "");

      var valGenerics = extractGenerics(val);

      var paths = valLower.split("::");
      removeEmptyStringsFromArray(paths);
      val = paths[paths.length - 1];
      var contains = paths.slice(0, paths.length > 1 ? paths.length - 1 : 1);

      var lev, j;
      for (j = 0; j < nSearchWords; ++j) {
        ty = searchIndex[j];
        if (!ty || (filterCrates !== undefined && ty.crate !== filterCrates)) {
          continue;
        }
        var lev_add = 0;
        if (paths.length > 1) {
          lev = checkPath(contains, paths[paths.length - 1], ty);
          if (lev > MAX_LEV_DISTANCE) {
            continue;
          } else if (lev > 0) {
            lev_add = lev / 10;
          }
        }

        returned = MAX_LEV_DISTANCE + 1;
        in_args = MAX_LEV_DISTANCE + 1;
        var index = -1;
        // we want lev results to go lower than others
        lev = MAX_LEV_DISTANCE + 1;
        fullId = ty.id;

        if (
          searchWords[j].indexOf(split[i]) > -1 ||
          searchWords[j].indexOf(val) > -1 ||
          ty.normalizedName.indexOf(val) > -1
        ) {
          // filter type: ... queries
          if (
            typePassesFilter(typeFilter, ty.ty) &&
            results[fullId] === undefined
          ) {
            index = ty.normalizedName.indexOf(val);
          }
        }
        if ((lev = levenshtein(searchWords[j], val)) <= MAX_LEV_DISTANCE) {
          if (typePassesFilter(typeFilter, ty.ty)) {
            lev += 1;
          } else {
            lev = MAX_LEV_DISTANCE + 1;
          }
        }
        in_args = findArg(ty, valGenerics, false, typeFilter);
        returned = checkReturned(ty, valGenerics, false, typeFilter);

        lev += lev_add;
        if (lev > 0 && val.length > 3 && searchWords[j].indexOf(val) > -1) {
          if (val.length < 6) {
            lev -= 1;
          } else {
            lev = 0;
          }
        }
        if (in_args <= MAX_LEV_DISTANCE) {
          if (results_in_args[fullId] === undefined) {
            results_in_args[fullId] = {
              id: j,
              index: index,
              lev: in_args,
            };
          }
          results_in_args[fullId].lev = Math.min(
            results_in_args[fullId].lev,
            in_args
          );
        }
        if (returned <= MAX_LEV_DISTANCE) {
          if (results_returned[fullId] === undefined) {
            results_returned[fullId] = {
              id: j,
              index: index,
              lev: returned,
            };
          }
          results_returned[fullId].lev = Math.min(
            results_returned[fullId].lev,
            returned
          );
        }
        if (
          typePassesFilter(typeFilter, ty.ty) &&
          (index !== -1 || lev <= MAX_LEV_DISTANCE)
        ) {
          if (index !== -1 && paths.length < 2) {
            lev = 0;
          }
          if (results[fullId] === undefined) {
            results[fullId] = {
              id: j,
              index: index,
              lev: lev,
            };
          }
          results[fullId].lev = Math.min(results[fullId].lev, lev);
        }
      }
    }

    var ret = {
      in_args: sortResults(results_in_args, true),
      returned: sortResults(results_returned, true),
      others: sortResults(results, false),
    };
    handleAliases(ret, query, filterCrates);
    return ret;
  }

  /**
   * Validate performs the following boolean logic. For example:
   * "File::open" will give IF A PARENT EXISTS => ("file" && "open")
   * exists in (name || path || parent) OR => ("file" && "open") exists in
   * (name || path )
   *
   * This could be written functionally, but I wanted to minimise
   * functions on stack.
   *
   * @param  {[string]} name   [The name of the result]
   * @param  {[string]} path   [The path of the result]
   * @param  {[string]} keys   [The keys to be used (["file", "open"])]
   * @param  {[object]} parent [The parent of the result]
   * @return {boolean}       [Whether the result is valid or not]
   */
  function validateResult(name, path, keys, parent) {
    for (var i = 0, len = keys.length; i < len; ++i) {
      // each check is for validation so we negate the conditions and invalidate
      if (
        !(
          // check for an exact name match
          (
            name.indexOf(keys[i]) > -1 ||
            // then an exact path match
            path.indexOf(keys[i]) > -1 ||
            // next if there is a parent, check for exact parent match
            (parent !== undefined &&
              parent.name !== undefined &&
              parent.name.toLowerCase().indexOf(keys[i]) > -1) ||
            // lastly check to see if the name was a levenshtein match
            levenshtein(name, keys[i]) <= MAX_LEV_DISTANCE
          )
        )
      ) {
        return false;
      }
    }
    return true;
  }

  function getQuery(raw) {
    var matches, type, query;
    query = raw;

    matches = query.match(
      /^(fn|mod|struct|enum|trait|type|const|macro)\s*:\s*/i
    );
    if (matches) {
      type = matches[1].replace(/^const$/, "constant");
      query = query.substring(matches[0].length);
    }

    return {
      raw: raw,
      query: query,
      type: type,
      id: query + type,
    };
  }

  function buildHrefAndPath(item) {
    var displayPath;
    var href;
    var type = itemTypes[item.ty];
    var name = item.name;
    var path = item.path;

    if (type === "mod") {
      displayPath = path + "::";
      href =
        window.rootPath + path.replace(/::/g, "/") + "/" + name + "/index.html";
    } else if (type === "primitive" || type === "keyword") {
      displayPath = "";
      href =
        window.rootPath +
        path.replace(/::/g, "/") +
        "/" +
        type +
        "." +
        name +
        ".html";
    } else if (type === "externcrate") {
      displayPath = "";
      href = window.rootPath + name + "/index.html";
    } else if (item.parent !== undefined) {
      var myparent = item.parent;
      var anchor = "#" + type + "." + name;
      var parentType = itemTypes[myparent.ty];
      var pageType = parentType;
      var pageName = myparent.name;

      if (parentType === "primitive") {
        displayPath = myparent.name + "::";
      } else if (type === "structfield" && parentType === "variant") {
        // Structfields belonging to variants are special: the
        // final path element is the enum name.
        var enumNameIdx = item.path.lastIndexOf("::");
        var enumName = item.path.substr(enumNameIdx + 2);
        path = item.path.substr(0, enumNameIdx);
        displayPath = path + "::" + enumName + "::" + myparent.name + "::";
        anchor = "#variant." + myparent.name + ".field." + name;
        pageType = "enum";
        pageName = enumName;
      } else {
        displayPath = path + "::" + myparent.name + "::";
      }
      href =
        window.rootPath +
        path.replace(/::/g, "/") +
        "/" +
        pageType +
        "." +
        pageName +
        ".html" +
        anchor;
    } else {
      displayPath = item.path + "::";
      href =
        window.rootPath +
        item.path.replace(/::/g, "/") +
        "/" +
        type +
        "." +
        name +
        ".html";
    }
    return [displayPath, href];
  }

  function pathSplitter(path) {
    var tmp = "<span>" + path.replace(/::/g, "::</span><span>");
    if (tmp.endsWith("<span>")) {
      return tmp.slice(0, tmp.length - 6);
    }
    return tmp;
  }

  function execSearch(query, searchWords, filterCrates) {
    function getSmallest(arrays, positions, notDuplicates) {
      var start = null;

      for (var it = 0, len = positions.length; it < len; ++it) {
        if (
          arrays[it].length > positions[it] &&
          (start === null || start > arrays[it][positions[it]].lev) &&
          !notDuplicates[arrays[it][positions[it]].fullPath]
        ) {
          start = arrays[it][positions[it]].lev;
        }
      }
      return start;
    }

    function mergeArrays(arrays) {
      var ret = [];
      var positions = [];
      var notDuplicates = {};

      for (var x = 0, arrays_len = arrays.length; x < arrays_len; ++x) {
        positions.push(0);
      }
      while (ret.length < MAX_RESULTS) {
        var smallest = getSmallest(arrays, positions, notDuplicates);

        if (smallest === null) {
          break;
        }
        for (x = 0; x < arrays_len && ret.length < MAX_RESULTS; ++x) {
          if (
            arrays[x].length > positions[x] &&
            arrays[x][positions[x]].lev === smallest &&
            !notDuplicates[arrays[x][positions[x]].fullPath]
          ) {
            ret.push(arrays[x][positions[x]]);
            notDuplicates[arrays[x][positions[x]].fullPath] = true;
            positions[x] += 1;
          }
        }
      }
      return ret;
    }

    // Split search query by ",", while respecting angle bracket nesting.
    // Since "<" is an alias for the Ord family of traits, it also uses
    // lookahead to distinguish "<"-as-less-than from "<"-as-angle-bracket.
    //
    // tokenizeQuery("A<B, C>, D") == ["A<B, C>", "D"]
    // tokenizeQuery("A<B, C, D") == ["A<B", "C", "D"]
    function tokenizeQuery(raw) {
      var i, matched;
      var l = raw.length;
      var depth = 0;
      var nextAngle = /(<|>)/g;
      var ret = [];
      var start = 0;
      for (i = 0; i < l; ++i) {
        switch (raw[i]) {
          case "<":
            nextAngle.lastIndex = i + 1;
            matched = nextAngle.exec(raw);
            if (matched && matched[1] === ">") {
              depth += 1;
            }
            break;
          case ">":
            if (depth > 0) {
              depth -= 1;
            }
            break;
          case ",":
            if (depth === 0) {
              ret.push(raw.substring(start, i));
              start = i + 1;
            }
            break;
        }
      }
      if (start !== i) {
        ret.push(raw.substring(start, i));
      }
      return ret;
    }

    var queries = tokenizeQuery(query.raw);
    var results = {
      in_args: [],
      returned: [],
      others: [],
    };

    for (var i = 0, len = queries.length; i < len; ++i) {
      query = queries[i].trim();
      if (query.length !== 0) {
        var tmp = execQuery(getQuery(query), searchWords, filterCrates);

        results.in_args.push(tmp.in_args);
        results.returned.push(tmp.returned);
        results.others.push(tmp.others);
      }
    }
    if (queries.length > 1) {
      return {
        in_args: mergeArrays(results.in_args),
        returned: mergeArrays(results.returned),
        others: mergeArrays(results.others),
      };
    }
    return {
      in_args: results.in_args[0],
      returned: results.returned[0],
      others: results.others[0],
    };
  }

  function buildIndex(rawSearchIndex) {
    searchIndex = [];
    var searchWords = [];
    var i, word;
    var currentIndex = 0;
    var id = 0;

    for (var crate in rawSearchIndex) {
      if (!hasOwnPropertyRustdoc(rawSearchIndex, crate)) {
        continue;
      }

      var crateSize = 0;

      searchWords.push(crate);
      // This object should have exactly the same set of fields as the "row"
      // object defined below. Your JavaScript runtime will thank you.
      // https://mathiasbynens.be/notes/shapes-ics
      var crateRow = {
        crate: crate,
        ty: 1, // == ExternCrate
        name: crate,
        path: "",
        desc: rawSearchIndex[crate].doc,
        parent: undefined,
        type: null,
        id: id,
        normalizedName:
          crate.indexOf("_") === -1 ? crate : crate.replace(/_/g, ""),
      };
      id += 1;
      searchIndex.push(crateRow);
      currentIndex += 1;

      // TODO: can we do this?
      var isNewVersion = !!rawSearchIndex[crate].t;

      // an array of (Number) item types
      var itemTypes = isNewVersion ? rawSearchIndex[crate].t : rawSearchIndex[crate].i.map(arr => arr[0]);
      // an array of (String) item names
      var itemNames = isNewVersion ? rawSearchIndex[crate].n : rawSearchIndex[crate].i.map(arr => arr[1]);
      // an array of (String) full paths (or empty string for previous path)
      var itemPaths = isNewVersion ? rawSearchIndex[crate].q : rawSearchIndex[crate].i.map(arr => arr[2]);
      // an array of (String) descriptions
      var itemDescs = isNewVersion ? rawSearchIndex[crate].d : rawSearchIndex[crate].i.map(arr => arr[3]);
      // an array of (Number) the parent path index + 1 to `paths`, or 0 if none
      var itemParentIdxs = isNewVersion ? rawSearchIndex[crate].i : rawSearchIndex[crate].i.map(arr => arr[4]);
      // an array of (Object | null) the type of the function, if any
      var itemFunctionSearchTypes = isNewVersion ? rawSearchIndex[crate].f : rawSearchIndex[crate].i.map(arr => arr[5]);
      // an array of [(Number) item type,
      //              (String) name]
      var paths = rawSearchIndex[crate].p || [];
      // an array of [(String) alias name
      //             [Number] index to items]
      var aliases = rawSearchIndex[crate].a || [];

      // convert `rawPaths` entries into object form
      var len = paths.length;
      for (i = 0; i < len; ++i) {
        paths[i] = {
          ty: paths[i][0],
          name: paths[i][1],
        };
      }

      // convert `item*` into an object form, and construct word indices.
      //
      // before any analysis is performed lets gather the search terms to
      // search against apart from the rest of the data.  This is a quick
      // operation that is cached for the life of the page state so that
      // all other search operations have access to this cached data for
      // faster analysis operations
      len = itemTypes.length;
      var lastPath = "";
      for (i = 0; i < len; ++i) {
        // This object should have exactly the same set of fields as the "crateRow"
        // object defined above.
        if (typeof itemNames[i] === "string") {
          word = itemNames[i].toLowerCase();
          searchWords.push(word);
        } else {
          word = "";
          searchWords.push("");
        }
        var row = {
          crate: crate,
          ty: itemTypes[i],
          name: itemNames[i],
          path: itemPaths[i] ? itemPaths[i] : lastPath,
          desc: itemDescs[i],
          parent:
            itemParentIdxs[i] > 0 ? paths[itemParentIdxs[i] - 1] : undefined,
          type: itemFunctionSearchTypes[i],
          id: id,
          normalizedName:
            word.indexOf("_") === -1 ? word : word.replace(/_/g, ""),
        };
        id += 1;
        searchIndex.push(row);
        lastPath = row.path;
        crateSize += 1;
      }

      if (aliases) {
        ALIASES[crate] = {};
        var j, local_aliases;
        for (var alias_name in aliases) {
          if (!hasOwnPropertyRustdoc(aliases, alias_name)) {
            continue;
          }

          if (!hasOwnPropertyRustdoc(ALIASES[crate], alias_name)) {
            ALIASES[crate][alias_name] = [];
          }
          local_aliases = aliases[alias_name];
          for (j = 0, len = local_aliases.length; j < len; ++j) {
            ALIASES[crate][alias_name].push(local_aliases[j] + currentIndex);
          }
        }
      }
      currentIndex += crateSize;
    }
    return searchWords;
  }

  index = buildIndex(rawSearchIndex);

  return (query) => {
    return execSearch(getQuery(query), index);
  };
}

exports.initSearch = initSearch;
