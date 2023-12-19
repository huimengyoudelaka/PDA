# 修改为新的终结符
from datetime import datetime


class Symbol:

    def __init__(self, name, terminal=True):
        self.name = name
        self.terminal = terminal

    def isTerminal(self):
        return self.terminal

    def getName(self):
        return self.name

    def equal(self, symbol):
        return self.getName() == symbol.getName() and self.isTerminal() == symbol.isTerminal()


class Productions:
    def __init__(self, left, right):
        self.left = Symbol(left, False)
        self.right = right

    def getLeft(self):
        return self.left

    def getRight(self):
        return self.right

    def updateRight(self, newRight):
        self.right = newRight

    def addProduction(self, right):
        for production in right.split('|'):
            rightSymbols = []
            if len(production) == 0:
                continue
            for symbol in production.split(','):
                if len(symbol) == 0:
                    continue
                flag = 'A' <= symbol[0] <= 'Z'
                rightSymbols.append(Symbol(symbol, not flag))
            if len(rightSymbols) != 0 and not self.has(rightSymbols):
                self.right.append(rightSymbols)

    def has(self, rightSymbols):
        for p in self.right:
            if len(rightSymbols) != len(p):
                continue
            flag = True
            for index, s in enumerate(p):
                if s.getName() != rightSymbols[index].getName():
                    flag = False
                    break
            if flag:
                return True
        return False

    def printInfo(self):
        for index, production in enumerate(self.right):
            # print(index)
            string = self.left.getName() + '->'
            for symbol in production:
                string += symbol.getName() + ","
            print(string)

    def reduceLeftRecursion(self, proDict, Vn, Vt, oderDict):
        deleteIndex = set()
        newProductions = []
        # 消除间接左递归
        for index, p in enumerate(self.right):
            if not p[0].isTerminal():
                if self.left.equal(p[0]):
                    deleteIndex.add(index)
                    newProductions.append(p[1:])
                elif oderDict[p[0].getName()] < oderDict[self.left.getName()]:
                    self.update(0, p, proDict[p[0].getName()].getRight())
                    deleteIndex.add(index)
        retainProductions = [i for index, i in enumerate(self.right) if index not in deleteIndex]
        # 消除直接左递归
        if len(newProductions) != 0:
            newSymbol = Symbol(self.left.getName() + datetime.now().strftime("%Y%m%d%H%M%S"), False)
            oderDict[newSymbol.getName()] = 0
            for p in newProductions:
                p.append(newSymbol)
            newProductions.append([Symbol('ε'), ])
            for p in retainProductions:
                p.append(newSymbol)
            Vn.add(newSymbol.getName())
            proDict[newSymbol.getName()] = Productions(newSymbol.getName(), newProductions)
        self.right = retainProductions

    def update(self, index, preProduction, productions):
        for production in productions:
            if (len(production) and production[0].getName() != 'ε') or len(preProduction) == 0:
                newProduction = preProduction[:index] + production + preProduction[index + 1:]
            else:
                newProduction = preProduction[:index] + preProduction[index + 1:]
            if len(newProduction) == 0:
                continue
            if not self.has(newProduction):
                self.right.append(newProduction)

    def updateSingel(self, productions):
        for production in productions:
            self.right.append(production)


class Grammar:
    def __init__(self, grammarPath):
        self.productions = {}
        self.Vt = set()  # 终结符
        self.Vn = set()  # 非终结符
        self.start = 'S'  # 一般都是这个
        with open(grammarPath, encoding='utf-8') as file:
            content = file.readlines()
            for production in content:
                if production[-1] == '\n':
                    production = production[:-1]
                left, right = production.split('->')
                if left not in self.Vn:
                    self.Vn.add(left)
                    self.productions[left] = Productions(left, [])
                self.productions[left].addProduction(right)
                for i in right.split('|'):
                    if len(i) == 0:
                        continue
                    for j in i.split(','):
                        if len(j) == 0:
                            continue
                        if not 'A' <= j[0] <= 'Z':
                            if j not in self.Vt and j != 'ε':
                                self.Vt.add(j)
                        else:
                            if j not in self.Vn:
                                self.Vn.add(j)
                                self.productions[j] = Productions(j, [])

    def printInfo(self):
        print('非终结符:', self.Vn)
        print('终结符:', self.Vt)
        print('开始符号:', self.start)
        print('产生式:')
        for p in self.productions.values():
            p.printInfo()

    def reduceLeftRecursion(self):
        orderVn = list(self.Vn)
        print('消除顺序:', orderVn)
        orderDic = {j: i for i, j in enumerate(orderVn)}
        for v in orderVn:
            self.productions[v].reduceLeftRecursion(self.productions, self.Vn, self.Vt, orderDic)

    def reduceNull(self):
        VnProductNull = set()
        while True:
            count = 0
            for p in self.productions.values():
                if p.getLeft().getName() in VnProductNull:
                    continue
                for r in p.getRight():
                    if r[0].getName() == 'ε':
                        count += 1
                        VnProductNull.add(p.getLeft().getName())
                        break
                    flag = True
                    for s in r:
                        if s.getName() not in VnProductNull:
                            flag = False
                            break
                    if flag:
                        count += 1
                        VnProductNull.add(p.getLeft().getName())
                        break
            if count == 0:
                break
        print('可空非终结符集合:', VnProductNull)
        for v in VnProductNull:
            self.productions[v].updateRight([r for r in self.productions[v].getRight() if r[0].getName() != 'ε'])
        if 'S' in VnProductNull:
            newS = 'S' + datetime.now().strftime("%Y%m%d%H%M%S")
            self.start = newS
            self.Vn.add(newS)
            self.productions[newS] = Productions(newS, [])
            self.productions[newS].addProduction('ε|S')
            VnProductNull.remove('S')
        for p in self.productions.values():
            for right in p.getRight():
                for index, symbol in enumerate(right):
                    if symbol.getName() in VnProductNull:
                        p.update(index, right, [[]])

    def reduceSingle(self):
        for p in self.productions.values():
            deleteSet = set()
            for index, r in enumerate(p.getRight()):
                if len(r) == 1 and not r[0].isTerminal() and not p.getLeft().equal(r[0]):
                    deleteSet.add(index)
                    p.updateSingel(self.productions[r[0].getName()].getRight())
            newR = [r for index, r in enumerate(p.getRight()) if index not in deleteSet]
            p.updateRight(newR)

    def reduceUnuseful(self):
        reachSet = set()
        reachSet.add(self.start)
        reachList = [self.productions[self.start], ]
        proSet = set(self.Vt)
        proSet.add('ε')
        while True:
            flag = True
            for v in reachList:
                for r in v.getRight():
                    for s in r:
                        if not s.isTerminal() and s.getName() not in reachSet:
                            reachSet.add(s.getName())
                            reachList.append(self.productions[s.getName()])
                            flag = False
            if flag:
                break
        while True:
            flag = True
            for v in self.productions.values():
                if v.getLeft().getName() in proSet:
                    continue
                for r in v.getRight():
                    pro = True
                    for s in r:
                        if s.getName() not in proSet:
                            pro = False
                            break
                    if pro:
                        proSet.add(v.getLeft().getName())
                        flag = False
                        break
            if flag:
                break
        print('可到达集合:', reachSet)
        print('可产生集合:', proSet)
        newPro = {}
        newVt = set()
        newVn = set()
        for p in self.productions.values():
            newR = []
            if p.getLeft().getName() not in reachSet or p.getLeft().getName() not in proSet:
                continue
            for r in p.getRight():
                flag = True
                for s in r:
                    if s.getName() not in proSet:
                        flag = False
                        break
                if flag:
                    newR.append(r)
            if len(newR) != 0:
                newP = Productions(p.getLeft().getName(), [])
                newP.update(0, [], newR)
                newPro[p.getLeft().getName()] = newP
                if p.getLeft().getName() not in newVn:
                    newVn.add(p.getLeft().getName())
                for r in newR:
                    for s in r:
                        if s.isTerminal() and s.getName() not in newVt and s.getName() != 'ε':
                            newVt.add(s.getName())
        self.productions = newPro
        self.Vn = newVn
        self.Vt = newVt

    def generateGreibach(self):
        for vn in self.productions.keys():
            deleteIndex = set()
            for index, p in enumerate(self.productions[vn].getRight()):
                if not p[0].isTerminal():
                    self.productions[vn].update(0, p, self.productions[p[0].getName()].getRight())
                    deleteIndex.add(index)
            self.productions[vn].updateRight(
                [i for index, i in enumerate(self.productions[vn].getRight()) if index not in deleteIndex])
        newVn = {}
        VnList = list(self.Vn)
        for v in VnList:
            for p in self.productions[v].getRight():
                if len(p) == 1:
                    continue
                for index, s in enumerate(p[1:], 1):
                    if 'a' <= s.getName()[0] <= 'z':
                        if s.getName() not in newVn:
                            newS = Symbol(chr(ord(s.getName()) - 32) + datetime.now().strftime("%Y%m%d%H%M%S"), False)
                            newVn[s.getName()] = newS
                            newP = Productions(newS.getName(), [[s], ])
                            self.productions[newS.getName()] = newP
                            self.Vn.add(newS.getName())
                        p[index] = newVn[s.getName()]


if __name__ == '__main__':
    print('******************文法初始化******************')
    a = Grammar('../grammar10.txt')
    a.printInfo()
    # print('******************消除左递归******************')
    # a.reduceLeftRecursion()
    # a.printInfo()
    print('******************消除空产生式******************')
    a.reduceNull()
    a.printInfo()
    # print('******************消除单一产生式******************')
    # a.reduceSingle()
    # a.printInfo()
    # print('******************消除无用符号******************')
    # a.reduceUnuseful()
    # a.printInfo()
    # print('******************构造Greibach范式******************')
    # a.generateGreibach()
    # a.printInfo()
